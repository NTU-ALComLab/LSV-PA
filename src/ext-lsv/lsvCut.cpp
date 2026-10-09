#include "lsvCut.h"
#ifdef ABC_USE_CUDD
#include "bdd/cudd/cuddInt.h"
#endif

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <set>
#include <utility>
#include <vector>

namespace {
using Cut = std::vector<int>;
using Cuts = std::vector<Cut>;

// Iterative postorder: stop at the cut boundary, and visit shared nodes once.
// The same routine gives a full topological order when the boundary is empty.
class ConeOrder {
 public:
  explicit ConeOrder(Abc_Ntk_t* network)
      : network_(network), seen_(Abc_NtkObjNumMax(network), 0), stamp_(0) {}

  void Begin() {
    if (++stamp_ == 0) {
      std::fill(seen_.begin(), seen_.end(), 0);
      stamp_ = 1;
    }
    order.clear();
  }

  void Add(Abc_Obj_t* root, const Cut& boundary) {
    if (seen_[Abc_ObjId(root)] == stamp_) return;
    std::vector<std::pair<Abc_Obj_t*, int>> stack;
    stack.emplace_back(root, 0);
    seen_[Abc_ObjId(root)] = stamp_;
    while (!stack.empty()) {
      Abc_Obj_t* node = stack.back().first;
      const int id = Abc_ObjId(node);
      const bool stop = std::binary_search(boundary.begin(), boundary.end(), id)
                        || node == Abc_AigConst1(network_) || Abc_ObjIsCi(node);
      if (stop || stack.back().second == 2) {
        order.push_back(node);
        stack.pop_back();
        continue;
      }
      const int edge = stack.back().second++;
      Abc_Obj_t* child = Abc_ObjFanin(node, edge);
      if (seen_[Abc_ObjId(child)] != stamp_) {
        seen_[Abc_ObjId(child)] = stamp_;
        stack.emplace_back(child, 0);
      }
    }
  }

  std::vector<Abc_Obj_t*> order;

 private:
  Abc_Ntk_t* network_;
  std::vector<unsigned> seen_;
  unsigned stamp_;
};

// Sorted set union, rejecting overlarge candidates as soon as possible.
bool Merge(const Cut& a, const Cut& b, int k, Cut& result) {
  result.clear();
  size_t i = 0, j = 0;
  while (i < a.size() || j < b.size()) {
    int id;
    if (j == b.size() || (i < a.size() && a[i] < b[j])) id = a[i++];
    else if (i == a.size() || b[j] < a[i]) id = b[j++];
    else { id = a[i]; ++i; ++j; }
    result.push_back(id);
    if (result.size() > static_cast<size_t>(k)) return false;
  }
  return true;
}

std::vector<Cuts> Enumerate(Abc_Ntk_t* network, int k) {
  std::vector<Cuts> cuts(Abc_NtkObjNumMax(network));
  // Constants have no independent input variable and thus have an empty cut.
  cuts[Abc_ObjId(Abc_AigConst1(network))].push_back(Cut());
  Abc_Obj_t* node;
  int i;
  Abc_NtkForEachCi(network, node, i)
    cuts[Abc_ObjId(node)].push_back(Cut(1, Abc_ObjId(node)));

  ConeOrder topo(network);
  topo.Begin();
  const Cut empty;
  Abc_NtkForEachNode(network, node, i) topo.Add(node, empty);
  for (Abc_Obj_t* root : topo.order) {
    if (!Abc_ObjIsNode(root)) continue;
    Cuts& dest = cuts[Abc_ObjId(root)];
    dest.push_back(Cut(1, Abc_ObjId(root)));
    std::set<Cut> unique;
    unique.insert(dest.front());
    Cut candidate;
    const Cuts& left = cuts[Abc_ObjFaninId0(root)];
    const Cuts& right = cuts[Abc_ObjFaninId1(root)];
    for (const Cut& a : left)
      for (const Cut& b : right)
        if (Merge(a, b, k, candidate) && unique.insert(candidate).second)
          dest.push_back(candidate);
    // Do not remove supersets: the assignment asks for all cuts. With
    // reconvergence, independently expanded fanin cuts may yield redundant
    // leaves; keep those unions too. Only identical leaf sets are deduplicated.
  }
  return cuts;
}

uint64_t Mask(size_t variables) {
  const unsigned bits = 1u << variables;
  // A shift by 64 is undefined; the six-variable case must be separate.
  return bits == 64 ? std::numeric_limits<uint64_t>::max()
                    : (uint64_t(1) << bits) - 1;
}

uint64_t Variable(size_t variables, size_t position) {
  uint64_t table = 0;
  const unsigned bits = 1u << variables;
  for (unsigned assignment = 0; assignment < bits; ++assignment)
    // The first (smallest-ID) variable is the MSB of the input assignment;
    // the assignment number itself selects the output table's bit position.
    if ((assignment >> (variables - 1 - position)) & 1u)
      table |= uint64_t(1) << assignment;
  return table;
}

bool TruthTable(Abc_Ntk_t* network, const Cut& cut,
                const std::vector<Abc_Obj_t*>& cone,
                std::vector<uint64_t>& values, uint64_t& result) {
  const uint64_t mask = Mask(cut.size());
  for (Abc_Obj_t* node : cone) {
    const int id = Abc_ObjId(node);
    const auto leaf = std::lower_bound(cut.begin(), cut.end(), id);
    if (leaf != cut.end() && *leaf == id)
      values[id] = Variable(cut.size(), leaf - cut.begin());
    else if (node == Abc_AigConst1(network)) values[id] = mask;
    else if (Abc_ObjIsCi(node)) return false; // An invalid cut missed a CI.
    else {
      uint64_t a = values[Abc_ObjFaninId0(node)];
      uint64_t b = values[Abc_ObjFaninId1(node)];
      if (Abc_ObjFaninC0(node)) a ^= mask;
      if (Abc_ObjFaninC1(node)) b ^= mask;
      values[id] = a & b;
    }
  }
  result = values[Abc_ObjId(cone.back())];
  return true;
}

#ifdef ABC_USE_CUDD
bool BddSize(Abc_Ntk_t* network, DdManager* manager, const Cut& cut,
             const std::vector<Abc_Obj_t*>& cone,
             std::vector<DdNode*>& values, int& result) {
  size_t referenced = 0;
  bool success = true;
  for (Abc_Obj_t* node : cone) {
    const int id = Abc_ObjId(node);
    const auto leaf = std::lower_bound(cut.begin(), cut.end(), id);
    DdNode* function = nullptr;
    if (leaf != cut.end() && *leaf == id)
      function = Cudd_bddIthVar(manager, static_cast<int>(leaf - cut.begin()));
    else if (node == Abc_AigConst1(network)) function = Cudd_ReadOne(manager);
    else if (!Abc_ObjIsCi(node)) {
      DdNode* a = values[Abc_ObjFaninId0(node)];
      DdNode* b = values[Abc_ObjFaninId1(node)];
      if (Abc_ObjFaninC0(node)) a = Cudd_Not(a);
      if (Abc_ObjFaninC1(node)) b = Cudd_Not(b);
      function = Cudd_bddAnd(manager, a, b);
    }
    if (!function) { success = false; break; }
    Cudd_Ref(function);
    values[id] = function;
    ++referenced;
  }
  if (success) result = Cudd_DagSize(values[Abc_ObjId(cone.back())]);
  // Balance every reference, including aliases and complemented pointers.
  for (size_t i = 0; i < referenced; ++i)
    Cudd_RecursiveDeref(manager, values[Abc_ObjId(cone[i])]);
  return success;
}
#endif
} // namespace

int Lsv_PrintCuts(Abc_Ntk_t* network, int k, bool bddSize) {
  if (!network || !Abc_NtkIsStrash(network) || k < 2 || k > 6) return 1;
#ifndef ABC_USE_CUDD
  if (bddSize) {
    Abc_Print(-1, "lsv_cut_bddsize requires an ABC build with CUDD.\n");
    return 1;
  }
#else
  DdManager* manager = nullptr;
  std::vector<DdNode*> bddValues;
  if (bddSize) {
    manager = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    if (!manager) {
      Abc_Print(-1, "Cannot initialize the BDD manager.\n");
      return 1;
    }
    // Index 0 is the smallest cut ID. Never reorder this private manager.
    Cudd_AutodynDisable(manager);
    bddValues.resize(Abc_NtkObjNumMax(network), nullptr);
  }
#endif
  const std::vector<Cuts> cuts = Enumerate(network, k);
  ConeOrder cone(network);
  std::vector<uint64_t> truthValues;
  if (!bddSize) truthValues.resize(Abc_NtkObjNumMax(network));
  Abc_Obj_t* node;
  int i, status = 0;
  Abc_NtkForEachNode(network, node, i) {
    for (const Cut& cut : cuts[Abc_ObjId(node)]) {
      cone.Begin();
      cone.Add(node, cut);
      uint64_t truth = 0;
      int size = 0;
      bool ok = false;
      if (!bddSize) ok = TruthTable(network, cut, cone.order, truthValues, truth);
#ifdef ABC_USE_CUDD
      else ok = BddSize(network, manager, cut, cone.order, bddValues, size);
#endif
      if (!ok) { status = 1; break; }
      std::printf("%d:", Abc_ObjId(node));
      for (int leaf : cut) std::printf(" %d", leaf);
      if (bddSize) std::printf(": %d\n", size);
      else std::printf(": %llX\n", static_cast<unsigned long long>(truth));
    }
    if (status) break;
  }
#ifdef ABC_USE_CUDD
  if (manager) Cudd_Quit(manager);
#endif
  if (status) Abc_Print(-1, "Cut evaluation failed (invalid boundary or BDD allocation failure).\n");
  return status;
}
