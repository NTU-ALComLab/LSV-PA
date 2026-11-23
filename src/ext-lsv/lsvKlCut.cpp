#include "lsvKlFlex.h"
#include "lsvCut.h"

#include <algorithm>
#include <functional>
#include <map>
#include <utility>

// A candidate cut (U, V) is validated in four steps, called in this order by GetKlCutSize:
//   1. WalkCutBoundary     K2; also collects the interior and leaves traversal marks
//   2. AllLeavesReached    first half of K3; reads the marks left by step 1
//   3. IsFanoutFree        K4; reads the marks left by step 1
//   4. AllLeavesNecessary  second half of K3; walks again, which overwrites the marks
// Steps 2 and 3 depend on the marks of step 1, so step 4 must come last.

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

// First half of K3: every leaf must have been reached by WalkCutBoundary. A leaf that was not
// reached is shielded by the other leaves on every path, so it could be removed: the cut is
// invalid.
static bool AllLeavesReached(Abc_Ntk_t *pNtk, const std::vector<int> &leaves)
{
  for (int id : leaves)
    if (!Abc_NodeIsTravIdCurrent(Abc_NtkObj(pNtk, id)))
      return false;
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

// Second half of K3: every leaf must be necessary.
// A reached PI leaf is the end of a root-to-PI path, so removing it always opens that path; it
// is necessary (this relies on AllLeavesReached having passed). For an AND leaf, remove it
// temporarily from remaining and run the K2 walk again: if the other leaves still block every
// path, the leaf is redundant. Re-inserting it at the same position keeps remaining sorted.
static bool AllLeavesNecessary(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  std::vector<int> remaining = cut.leaves;
  for (std::size_t i = 0; i < cut.leaves.size(); ++i)
  {
    if (Abc_ObjIsPi(Abc_NtkObj(pNtk, cut.leaves[i])))
      continue;
    remaining.erase(remaining.begin() + i);
    if (WalkCutBoundary(pNtk, cut.roots, remaining))
      return false;
    remaining.insert(remaining.begin() + i, cut.leaves[i]);
  }
  return true;
}

// Validates a cut that already satisfies K1. Returns -1 if K2, K3 or K4 fails, and otherwise
// the cut size |V| + |interior|. See the top of the file for why the checks run in this order.
static int GetKlCutSize(Abc_Ntk_t *pNtk, const KlCut &cut)
{
  std::vector<int> interior;
  if (!WalkCutBoundary(pNtk, cut.roots, cut.leaves, &interior)) // K2
    return -1;
  if (!AllLeavesReached(pNtk, cut.leaves)) // K3, first half
    return -1;
  if (!IsFanoutFree(pNtk, cut.leaves, interior)) // K4
    return -1;
  if (!AllLeavesNecessary(pNtk, cut)) // K3, second half
    return -1;
  return static_cast<int>(cut.roots.size() + interior.size());
}

// Leaf-set candidates U, each with its cone sum. cone(r, C) is the number of AND nodes passed
// when walking from root r down to its PA1 cut C (r itself excluded). U is the union of one cut
// C_r per selected root r. Every interior node is reached from some root r along a path that
// avoids U, hence also avoids C_r, so it lies in cone(r, C_r). Therefore |V| + cone sum is an
// upper bound on the size of (U, V). The same U can come from different cut combinations; each
// gives a valid bound, so the smallest one is kept.
typedef std::map<Cut, int> LeafUnions;

// Keeps only the leaf sets that are minimal under inclusion; a larger one is dropped together
// with its whole subtree. Every U is a union of PA1 cuts of the roots, so it is a cut of V.
// Let U1 be a strict subset of U2, and write + for set union. When a root r with a cut C is
// added below, U1 + C is a cut of the new roots and is contained in U2 + C:
//   - if U2 + C is strictly larger, its extra leaves can be removed and it stays a cut, so it
//     violates K3 and is invalid;
//   - if both are equal, the same leaf set is generated from U1 as well, so nothing is lost.
// Since U1 + C is a subset of U2 + C, it also passes the leaf limit, the signature test and K1.
// By induction, the leaf set of every valid cut still appears under its root set.
// Processing the sets by increasing size, comparing with the kept sets is enough: a dropped set
// itself contains some kept set.
static void KeepMinimalUnions(LeafUnions &unions)
{
  std::vector<LeafUnions::iterator> bySize;
  for (auto it = unions.begin(); it != unions.end(); ++it)
    bySize.push_back(it);
  std::stable_sort(bySize.begin(), bySize.end(),
                   [](LeafUnions::iterator a, LeafUnions::iterator b)
                   { return a->first.leaves.size() < b->first.leaves.size(); });

  std::vector<const Cut *> kept;
  for (LeafUnions::iterator it : bySize)
  {
    const Cut &u = it->first;
    bool hasSubset = false;
    for (const Cut *s : kept)
    {
      // Sets of equal size cannot be strict subsets. A signature bit set in s but not in u means
      // that s has a leaf that u lacks.
      if (s->leaves.size() < u.leaves.size() && !(s->sign & ~u.sign) &&
          std::includes(u.leaves.begin(), u.leaves.end(), s->leaves.begin(), s->leaves.end()))
      {
        hasSubset = true;
        break;
      }
    }
    if (hasSubset)
      unions.erase(it);
    else
      kept.push_back(&u);
  }
}

// One PA1 cut a root may use, with its cone size (AND nodes between the root and the cut).
struct RootOption
{
  Cut cut;
  int cone = 0;
};

// State shared by the whole search; it is passed down the recursion by reference.
// andIds, options and futureGain are prepared before the search; roots grows and shrinks with
// the current branch.
struct KlCutSearch
{
  Abc_Ntk_t *pNtk = nullptr;
  int k = 0;                                   // maximum number of leaves
  int l = 0;                                   // maximum number of roots
  std::vector<int> andIds;                     // IDs of the AND nodes that may be roots, ascending
  std::vector<std::vector<RootOption>> options; // options[index]: PA1 cuts of andIds[index], by decreasing cone
  // futureGain[index][t]: how much the bound can still grow by picking t more roots from
  // andIds[index] onwards. Picking root r adds 1 to |V| and at most r's largest cone to the cone
  // sum, so this is the sum of the t largest values of (1 + largest cone) in that suffix.
  std::vector<std::vector<int>> futureGain;
  std::vector<int> roots;                      // roots selected on the current branch
  int maximumSize = 0;                         // largest valid cut size found so far
  std::vector<KlCut> maximumCuts;              // all valid cuts tied at maximumSize
};

// Tries every way of adding one more root to search.roots. start is the first andIds index
// that may be picked; leafUnions holds the leaf-set candidates before the new root is added.
// Results are written to search.
//
// Subtree bound: a pair (U, option) produces a cut whose size, and the size of every cut grown
// from it by adding more roots, is at most
//   |V| + cone sum + futureGain   (the most that the remaining roots can still add).
// If this is below the current maximum, neither the pair nor its subtree can be printed, so the
// pair is not even merged. On the last level (l roots already, or no AND node left to pick)
// futureGain is 0 and only the cut itself counts.
// Leaf sets are sorted by decreasing cone sum and options by decreasing cone, so the bound only
// decreases along both loops, while maximumSize only grows: once the bound is too small, all
// later ones are too, and the loop can break.
// A leaf set reached through several paths has a size bounded by the bound of every path, so
// skipping it on one path loses nothing. KeepMinimalUnions drops a larger leaf set only when the
// smaller one is actually kept in nextUnions, so the skipping does not break it either.
static void EnumerateKlCuts(KlCutSearch &search, std::size_t start,
                            const LeafUnions &leafUnions)
{
  if (leafUnions.empty())
    return;
  std::vector<LeafUnions::const_iterator> byConeSum;
  for (auto it = leafUnions.begin(); it != leafUnions.end(); ++it)
    byConeSum.push_back(it);
  std::stable_sort(byConeSum.begin(), byConeSum.end(),
                   [](LeafUnions::const_iterator a, LeafUnions::const_iterator b)
                   { return a->second > b->second; });
  const int maxConeSum = byConeSum.front()->second;

  for (std::size_t index = start; index < search.andIds.size(); ++index)
  {
    int root = search.andIds[index];
    // options are the PA1 cuts of the new root; rootCount is |V| after adding it.
    const std::vector<RootOption> &options = search.options[index];
    const int rootCount = static_cast<int>(search.roots.size()) + 1;
    const bool lastLevel = rootCount == search.l || index + 1 == search.andIds.size();
    const int maxCone = options.empty() ? 0 : options.front().cone;
    // reach is |V| plus the most the subtree can still add; adding the cone sum gives the bound.
    int reach = rootCount;
    if (!lastLevel)
    {
      const std::vector<int> &gains = search.futureGain[index + 1];
      reach += gains[std::min<std::size_t>(static_cast<std::size_t>(search.l - rootCount), gains.size() - 1)];
    }

    // Even the best leaf set with the largest cone is not enough: skip this root entirely.
    if (reach + maxConeSum + maxCone < search.maximumSize)
      continue;
    search.roots.push_back(root);

    // nextUnions collects the leaf sets of the new root set.
    LeafUnions nextUnions;
    Cut merged;
    for (LeafUnions::const_iterator unionIt : byConeSum)
    {
      const Cut &leaves = unionIt->first;
      const int coneSum = unionIt->second;
      if (reach + coneSum + maxCone < search.maximumSize)
        break;
      if (std::binary_search(leaves.leaves.begin(), leaves.leaves.end(), root))
        continue;
      for (const RootOption &option : options)
      {
        int bound = coneSum + option.cone;
        if (reach + bound < search.maximumSize)
          break;

        // Cheap signature filter first, then the exact union. merged is a separate buffer
        // because Lsv_CutMerge clears its output first.
        if (__builtin_popcountll(leaves.sign | option.cut.sign) > search.k)
          continue;
        Lsv_CutMerge(leaves, option.cut, merged);
        if (merged.leaves.size() > static_cast<std::size_t>(search.k))
          continue;

        // K1 requires U and V to be disjoint: no selected root may appear among the merged
        // leaves. This also filters the trivial cut {root} of the new root.
        bool overlapsRoot = false;
        for (int selectedRoot : search.roots)
        {
          if (std::binary_search(merged.leaves.begin(), merged.leaves.end(), selectedRoot))
          {
            overlapsRoot = true;
            break;
          }
        }
        if (overlapsRoot)
          continue;

        // Each leaf set is validated once per root set. For a repeated one, only lower its cone
        // sum, which tightens the bound on the next level.
        auto [it, inserted] = nextUnions.emplace(merged, bound);
        if (!inserted)
        {
          it->second = std::min(it->second, bound);
          continue;
        }

        // The cut itself cannot reach the current maximum: skip validation. The comparison is
        // strict because tied cuts must be printed too. Below the last level the leaf set is
        // already in nextUnions, so the recursion still grows it with more roots.
        if (rootCount + bound < search.maximumSize)
          continue;

        // A larger valid cut replaces the previous answers; a tied one is added to them.
        KlCut candidate{search.roots, merged.leaves};
        int size = GetKlCutSize(search.pNtk, candidate);
        if (size > search.maximumSize)
        {
          search.maximumSize = size;
          search.maximumCuts.clear();
        }
        if (size == search.maximumSize)
          search.maximumCuts.push_back(std::move(candidate));
      }
    }

    // The next level only picks later IDs, so each root set is generated in one order only.
    // nextUnions keeps every leaf set that passed K1, even invalid ones: adding a root may fix a
    // K4 violation. Non-minimal leaf sets are dropped first, see KeepMinimalUnions.
    if (!lastLevel && !nextUnions.empty())
    {
      KeepMinimalUnions(nextUnions);
      EnumerateKlCuts(search, index + 1, nextUnions);
    }

    // Undo the choice and let the loop try the next root on this level.
    search.roots.pop_back();
  }
}

// Enumerates the PA1 cuts of every node, prepares the bounds and runs the search.
// k and l bound the numbers of leaves and roots; returns every valid cut of maximum size.
std::vector<KlCut> Lsv_FindMaximumKlCuts(Abc_Ntk_t *pNtk, int k, int l)
{
  if (l == 0)
    return {};

  KlCutSearch search;
  search.pNtk = pNtk;
  search.k = k;
  search.l = l;
  CutTable singleRootCuts = Lsv_NtkEnumCuts(pNtk, k);

  Abc_Obj_t *node;
  int i;
  Abc_AigForEachAnd(pNtk, node, i)
    search.andIds.push_back(Abc_ObjId(node));

  // Compute the cone size of every (root, PA1 cut) pair for the bounds, and sort each root's
  // options by decreasing cone. Meanwhile validate every single-root cut to seed maximumSize:
  // these cuts have |V| = 1 <= l, so the true maximum is at least this value, and pruning works
  // from the start instead of waiting for a large cut to turn up.
  // maximumCuts stays empty: the full search generates these cuts again and records them if they
  // are tied with the maximum, so nothing is recorded twice.
  for (int root : search.andIds)
  {
    std::vector<RootOption> &options = search.options.emplace_back();
    for (const Cut &cut : singleRootCuts.at(root))
    {
      std::vector<int> interior;
      WalkCutBoundary(pNtk, {root}, cut.leaves, &interior);
      options.push_back(RootOption{cut, static_cast<int>(interior.size())});
      if (std::binary_search(cut.leaves.begin(), cut.leaves.end(), root))
        continue; // the trivial cut {root} violates K1
      search.maximumSize = std::max(search.maximumSize,
                                    GetKlCutSize(pNtk, KlCut{{root}, cut.leaves}));
    }
    std::stable_sort(options.begin(), options.end(),
                     [](const RootOption &a, const RootOption &b) { return a.cone > b.cone; });
  }

  // Build futureGain from the back, keeping the largest values of (1 + largest cone) seen so far.
  // No more roots than AND nodes can be picked, so t is capped at min(l, number of ANDs) to avoid
  // wasting memory when l is large.
  const std::size_t n = search.andIds.size();
  const int maxPicks = static_cast<int>(std::min<std::size_t>(static_cast<std::size_t>(l), n));
  search.futureGain.assign(n + 1, std::vector<int>(maxPicks + 1, 0));
  std::vector<int> top; // decreasing, at most maxPicks values
  for (std::size_t index = n; index-- > 0;)
  {
    const std::vector<RootOption> &options = search.options[index];
    int gain = 1 + (options.empty() ? 0 : options.front().cone);
    top.insert(std::upper_bound(top.begin(), top.end(), gain, std::greater<int>()), gain);
    if (static_cast<int>(top.size()) > maxPicks)
      top.pop_back();
    for (int t = 1; t <= maxPicks; ++t)
      search.futureGain[index][t] = search.futureGain[index][t - 1] +
                                    (t - 1 < static_cast<int>(top.size()) ? top[t - 1] : 0);
  }

  // Start with no root selected: the only leaf-set candidate is the empty set, with cone sum 0.
  EnumerateKlCuts(search, 0, {{Cut{}, 0}});
  return std::move(search.maximumCuts);
}
