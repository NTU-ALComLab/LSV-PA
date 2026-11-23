#include "lsvKlFlex.h"
#include "lsvCut.h"

#include <algorithm>
#include <functional>
#include <map>
#include <utility>

// Walks from the roots towards the PIs along fanin edges and stops at the leaves (check K2).
// Returns false as soon as it reaches a PI that is not a leaf, i.e. a root-to-PI path avoids U.
// If interior is given, every AND node visited strictly between the roots and the leaves is
// appended to it; the interior is needed for K4 and for the cut size.
static bool WalkCutBoundary(Abc_Ntk_t *pNtk, const std::vector<int> &roots,
                     const std::vector<int> &leaves, std::vector<int> *interior = nullptr)
{
  // A fresh traversal ID resets every visited mark in O(1); shared nodes are expanded once.
  // pending is the DFS stack of node IDs: it starts with all roots and receives the fanins of
  // every expanded node.
  Abc_NtkIncrementTravId(pNtk);
  std::vector<int> pending = roots;
  while (!pending.empty())
  {
    int id = pending.back();
    pending.pop_back();
    Abc_Obj_t *node = Abc_NtkObj(pNtk, id);
    if (Abc_NodeIsTravIdCurrent(node))
      continue;
    // Mark before the leaf test, so that AllLeavesReached can tell which leaves were reached.
    Abc_NodeSetTravIdCurrent(node);
    if (std::binary_search(leaves.begin(), leaves.end(), id))
      continue;
    if (Abc_ObjIsPi(node))
      return false;
    if (Abc_AigNodeIsConst(node))
      continue;

    // A root may lie in the fanin cone of another root, so the walk passes through roots too.
    // Only the AND nodes between the roots and the leaves belong to the interior.
    if (interior && !std::binary_search(roots.begin(), roots.end(), id))
      interior->push_back(id);
    Abc_Obj_t *fanin;
    int i;
    Abc_ObjForEachFanin(node, fanin, i)
        pending.push_back(Abc_ObjId(fanin));
  }
  return true;
}

// K4: every fanout of an interior node must be an interior node or a root.
// The nodes marked by WalkCutBoundary are exactly the roots, the interior and the reached
// leaves, so "marked and not a leaf" means "in V or in the interior"; no sorting or searching
// of the interior is needed. POs are never marked, so an interior node driving a PO fails here.
// The leaf test is required: a leaf may have an interior node as its fanin, and such a leaf is
// marked although it is outside the cut.
static bool IsFanoutFree(Abc_Ntk_t *pNtk, const std::vector<int> &leaves,
                         const std::vector<int> &interior)
{
  for (int id : interior)
  {
    Abc_Obj_t *fanout;
    int i;
    Abc_ObjForEachFanout(Abc_NtkObj(pNtk, id), fanout, i)
    {
      if (!Abc_NodeIsTravIdCurrent(fanout) ||
          std::binary_search(leaves.begin(), leaves.end(), Abc_ObjId(fanout)))
        return false;
    }
  }
  return true;
}

// A PA1 cut together with its exact AND region, including its root.
struct RootOption
{
  Cut cut;
  std::vector<int> region;
  std::vector<int> fixedExits;
};

struct MaximumRegion
{
  KlCut base;
  std::vector<int> interior;
};

struct IndexedOption
{
  std::size_t rootIndex;
  const RootOption *option;
};

struct KlCutSearch
{
  Abc_Ntk_t *pNtk = nullptr;
  int k = 0;
  std::size_t rootLimit = 0;
  std::vector<int> andIds;
  std::vector<std::vector<RootOption>> options;
  std::vector<std::vector<IndexedOption>> optionsByFirstLeaf;
  std::vector<IndexedOption> leaflessOptions;
  std::vector<std::vector<std::size_t>> futureGain;
  std::vector<int> exits; // -1 outside the region, otherwise the number of external fanout edges
  std::vector<int> region;
  std::vector<int> roots;
  std::size_t exitCount = 0;
  std::map<Cut, bool> necessaryLeaves;
  std::size_t maximumSize = 0;
  std::vector<MaximumRegion> maximumRegions;
};

// Insert new ANDs once, updating the exact size and the outgoing boundary.
// Nodes with no fanouts count as exits so a dangling cone can still be represented.
static void AddRegion(KlCutSearch &search, const std::vector<int> &nodes)
{
  for (int id : nodes)
  {
    if (search.exits[id] >= 0)
      continue;
    Abc_Obj_t *node = Abc_NtkObj(search.pNtk, id);
    int external = (Abc_ObjFanoutNum(node) == 0);
    Abc_Obj_t *neighbor;
    int i;
    Abc_ObjForEachFanout(node, neighbor, i)
      external += search.exits[Abc_ObjId(neighbor)] < 0;
    search.exits[id] = external;
    search.exitCount += external > 0;
    search.region.push_back(id);

    Abc_ObjForEachFanin(node, neighbor, i)
    {
      int &count = search.exits[Abc_ObjId(neighbor)];
      if (count >= 0 && --count == 0)
        --search.exitCount;
    }
  }
}

// Undo only nodes added by this option, in reverse order.
static void RestoreRegion(KlCutSearch &search, std::size_t size)
{
  while (search.region.size() > size)
  {
    int id = search.region.back();
    search.region.pop_back();
    search.exitCount -= search.exits[id] > 0;
    search.exits[id] = -1;
    Abc_Obj_t *node = Abc_NtkObj(search.pNtk, id);
    Abc_Obj_t *fanin;
    int i;
    Abc_ObjForEachFanin(node, fanin, i)
    {
      int &count = search.exits[Abc_ObjId(fanin)];
      if (count >= 0 && count++ == 0)
        ++search.exitCount;
    }
  }
}

// Every leaf has already been reached along one of its local regions. K3 now
// asks whether each leaf has a path to a PI avoiding the other leaves. That
// part of the path depends only on U, so different regions can reuse the result.
static bool HasNecessaryLeaves(KlCutSearch &search, const Cut &cut)
{
  std::vector<int> andLeaves;
  for (int id : cut.leaves)
    if (!Abc_ObjIsPi(Abc_NtkObj(search.pNtk, id)))
      andLeaves.push_back(id);
  if (andLeaves.empty())
    return true;

  auto cached = search.necessaryLeaves.find(cut);
  if (cached != search.necessaryLeaves.end())
    return cached->second;
  bool necessary = true;
  std::vector<int> remaining = cut.leaves;
  for (int leaf : andLeaves)
  {
    auto position = std::lower_bound(remaining.begin(), remaining.end(), leaf) - remaining.begin();
    remaining.erase(remaining.begin() + position);
    if (WalkCutBoundary(search.pNtk, {leaf}, remaining))
    {
      necessary = false;
      break;
    }
    remaining.insert(remaining.begin() + position, leaf);
  }
  // Bound the optional cache. Beyond this point we still perform every check.
  if (search.necessaryLeaves.size() < 65536)
    search.necessaryLeaves.emplace(cut, necessary);
  return necessary;
}

static void RememberRegion(KlCutSearch &search, const Cut &leaves)
{
  const std::size_t size = search.region.size();
  if (size < search.maximumSize || search.exitCount != search.roots.size() ||
      !HasNecessaryLeaves(search, leaves))
    return;
  if (size > search.maximumSize)
  {
    search.maximumSize = size;
    search.maximumRegions.clear();
  }
  MaximumRegion answer{{search.roots, leaves.leaves}, {}};
  for (int id : search.region)
    if (search.exits[id] == 0)
      answer.interior.push_back(id);
  std::sort(answer.interior.begin(), answer.interior.end());
  search.maximumRegions.push_back(std::move(answer));
}

// Both regions must stop at the merged leaves. If one region contains a
// leaf from the other, its stored node set would overcount the merged region.
static bool CanJoinRegion(const KlCutSearch &search, int root, const Cut &leaves,
                          const RootOption &option)
{
  for (int id : option.cut.leaves)
    if (search.exits[id] >= 0)
      return false;
  for (int id : leaves.leaves)
    if (std::binary_search(option.region.begin(), option.region.end(), id))
      return false;
  // A PO exit cannot disappear when the region grows. If its ID is already
  // behind the search position, it must already have been selected as a root.
  for (int id : option.fixedExits)
    if (id < root && !std::binary_search(search.roots.begin(), search.roots.end(), id))
      return false;
  return true;
}

static void EnumerateBaseCuts(KlCutSearch &search, std::size_t start, const Cut &leaves);

// The root is already selected. Add the option temporarily, evaluate its
// boundary and grow it, then restore the region for the next option.
static void VisitRegion(KlCutSearch &search, std::size_t index, const RootOption &option,
                        const Cut &merged, std::size_t previousSize, std::size_t future)
{
  AddRegion(search, option.region);
  if (search.region.size() + future >= search.maximumSize)
  {
    // A selected root with all fanouts inside cannot become an exit again.
    bool rootsExposed = true;
    for (int root : search.roots)
      if (search.exits[root] == 0)
      {
        rootsExposed = false;
        break;
      }
    if (rootsExposed)
    {
      RememberRegion(search, merged);
      if (search.roots.size() < search.rootLimit && index + 1 < search.andIds.size())
        EnumerateBaseCuts(search, index + 1, merged);
    }
  }
  RestoreRegion(search, previousSize);
}

// With |U| == k, a new PA1 cut must be a subset of U, so its smallest leaf
// must be in U. Each option is indexed by that leaf once. The full subset
// test is still needed, and every passing option keeps U unchanged.
static void VisitIndexedOptions(KlCutSearch &search, std::size_t start, const Cut &leaves,
                                const std::vector<IndexedOption> &bucket)
{
  const std::size_t previousSize = search.region.size();
  const std::size_t available = search.rootLimit - search.roots.size();
  auto first = std::lower_bound(bucket.begin(), bucket.end(), start,
    [](const IndexedOption &entry, std::size_t index) { return entry.rootIndex < index; });
  for (auto it = first; it != bucket.end(); ++it)
  {
    std::size_t index = it->rootIndex;
    int root = search.andIds[index];
    const RootOption &option = *it->option;
    const std::size_t future = search.futureGain[index + 1][available - 1];
    if (search.exits[root] == 0 || previousSize + option.region.size() + future < search.maximumSize ||
        (option.cut.sign & ~leaves.sign) ||
        !std::includes(leaves.leaves.begin(), leaves.leaves.end(),
                       option.cut.leaves.begin(), option.cut.leaves.end()) ||
        !CanJoinRegion(search, root, leaves, option))
      continue;
    search.roots.push_back(root);
    VisitRegion(search, index, option, leaves, previousSize, future);
    search.roots.pop_back();
  }
}

// For a valid final U, each root's first-hit leaves form a minimal local cut.
// Indeed, every reached leaf has a tail to a PI avoiding the rest of U (K3).
// Thus every valid KL cut has a decomposition whose local regions avoid U.
// Rejecting a pair when either option enters the other's leaves only removes
// noncanonical decompositions. On the remaining paths the exact region grows
// by set union, and the local option for each root is determined by (V,U).
static void EnumerateBaseCuts(KlCutSearch &search, std::size_t start, const Cut &leaves)
{
  const std::size_t previousSize = search.region.size();
  const std::size_t available = search.rootLimit - search.roots.size();
  if (previousSize + search.futureGain[start][available] < search.maximumSize)
    return;

  if (leaves.leaves.size() == static_cast<std::size_t>(search.k))
  {
    for (int id : leaves.leaves)
      VisitIndexedOptions(search, start, leaves, search.optionsByFirstLeaf[id]);
    VisitIndexedOptions(search, start, leaves, search.leaflessOptions);
    return;
  }

  for (std::size_t index = start; index < search.andIds.size(); ++index)
  {
    int root = search.andIds[index];
    const auto &options = search.options[index];
    if (options.empty() || search.exits[root] == 0 ||
        std::binary_search(leaves.leaves.begin(), leaves.leaves.end(), root))
      continue;
    const std::size_t future = search.futureGain[index + 1][available - 1];
    if (previousSize + options.front().region.size() + future < search.maximumSize)
      continue;
    search.roots.push_back(root);

    Cut merged;
    for (const RootOption &option : options)
    {
      if (previousSize + option.region.size() + future < search.maximumSize)
        break;
      if (__builtin_popcountll(leaves.sign | option.cut.sign) > search.k)
        continue;
      if (!CanJoinRegion(search, root, leaves, option))
        continue;
      Lsv_CutMerge(leaves, option.cut, merged);
      if (merged.leaves.size() > static_cast<std::size_t>(search.k))
        continue;

      VisitRegion(search, index, option, merged, previousSize, future);
    }
    search.roots.pop_back();
  }
}

// Promoting an interior node leaves the region and U unchanged. K4 still
// holds, and K3's existing witnesses remain. Enumerate only after finding
// the maximum size, so promotions of smaller regions are never generated.
static void AppendRootPromotions(const MaximumRegion &region, std::size_t start,
                                 std::size_t rootLimit, KlCut &cut,
                                 std::vector<KlCut> &maximumCuts)
{
  maximumCuts.push_back(cut);
  if (cut.roots.size() == rootLimit)
    return;
  for (std::size_t i = start; i < region.interior.size(); ++i)
  {
    int id = region.interior[i];
    auto pos = std::lower_bound(cut.roots.begin(), cut.roots.end(), id) - cut.roots.begin();
    cut.roots.insert(cut.roots.begin() + pos, id);
    AppendRootPromotions(region, i + 1, rootLimit, cut, maximumCuts);
    cut.roots.erase(cut.roots.begin() + pos);
  }
}

std::vector<KlCut> Lsv_FindMaximumKlCuts(Abc_Ntk_t *pNtk, int k, int l)
{
  if (l == 0)
    return {};

  KlCutSearch search;
  search.pNtk = pNtk;
  search.k = k;
  search.exits.assign(Abc_NtkObjNumMax(pNtk), -1);
  const CutTable singleRootCuts = Lsv_NtkEnumCuts(pNtk, k);
  Abc_Obj_t *node;
  int i;
  Abc_AigForEachAnd(pNtk, node, i)
    search.andIds.push_back(Abc_ObjId(node));
  const std::size_t n = search.andIds.size();
  search.rootLimit = std::min(static_cast<std::size_t>(l), n);
  if (search.rootLimit == 0)
    return {};
  search.region.reserve(n);

  for (int root : search.andIds)
  {
    auto &options = search.options.emplace_back();
    for (const Cut &cut : singleRootCuts.at(root))
    {
      if (std::binary_search(cut.leaves.begin(), cut.leaves.end(), root))
        continue;
      RootOption option{cut, {}, {}};
      if (!WalkCutBoundary(pNtk, {root}, cut.leaves, &option.region))
        continue;
      if (option.region.size() + 1 > search.maximumSize &&
          IsFanoutFree(pNtk, cut.leaves, option.region) && HasNecessaryLeaves(search, cut))
        search.maximumSize = option.region.size() + 1;
      option.region.push_back(root);
      std::sort(option.region.begin(), option.region.end());
      for (int id : option.region)
      {
        Abc_Obj_t *gate = Abc_NtkObj(pNtk, id);
        if (!Abc_ObjFanoutNum(gate))
          option.fixedExits.push_back(id);
        else
        {
          Abc_Obj_t *fanout;
          Abc_ObjForEachFanout(gate, fanout, i)
          {
            if (Abc_ObjIsPo(fanout))
            {
              option.fixedExits.push_back(id);
              break;
            }
          }
        }
      }
      options.push_back(std::move(option));
    }
    std::stable_sort(options.begin(), options.end(), [](const RootOption &a, const RootOption &b) {
      return a.region.size() > b.region.size();
    });
  }

  // Build after sorting all options so pointers remain valid. Appending in
  // increasing root index order lets the search skip earlier roots in a bucket.
  search.optionsByFirstLeaf.resize(Abc_NtkObjNumMax(pNtk));
  for (std::size_t index = 0; index < n; ++index)
    for (const RootOption &option : search.options[index])
    {
      auto &bucket = option.cut.leaves.empty() ? search.leaflessOptions
                                                  : search.optionsByFirstLeaf[option.cut.leaves.front()];
      bucket.push_back({index, &option});
    }

  // Summing region lengths overestimates a union when the regions overlap,
  // so the t largest remaining lengths give a safe subtree upper bound.
  search.futureGain.assign(n + 1, std::vector<std::size_t>(search.rootLimit + 1, 0));
  std::vector<std::size_t> top;
  for (std::size_t index = n; index-- > 0;)
  {
    const auto &options = search.options[index];
    const auto gain = options.empty() ? std::size_t{0} : options.front().region.size();
    top.insert(std::upper_bound(top.begin(), top.end(), gain, std::greater<std::size_t>()), gain);
    if (top.size() > search.rootLimit)
      top.pop_back();
    for (std::size_t t = 1; t <= search.rootLimit; ++t)
      search.futureGain[index][t] = search.futureGain[index][t - 1] + (t <= top.size() ? top[t - 1] : 0);
  }

  // Every non-boundary node of a DAG region reaches an exit within that
  // region. Walking from the base roots thus reconstructs the full region.
  EnumerateBaseCuts(search, 0, Cut{});
  std::vector<KlCut> maximumCuts;
  for (const MaximumRegion &region : search.maximumRegions)
  {
    KlCut expanded = region.base;
    AppendRootPromotions(region, 0, search.rootLimit, expanded, maximumCuts);
  }
  return maximumCuts;
}
