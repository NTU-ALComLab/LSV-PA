/**
 * PA1 Exercise 4: enumerate k-feasible cuts and evaluate their functions.
 *
 * All cut-specific data structures and algorithms below are implemented here.
 * ABC supplies only network accessors; CUDD supplies general BDD operations.
 * No ABC cut-enumeration, cut truth-table, or cut-BDD helpers are used.
 */

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace {

constexpr int kMaxLeaves = 6;  // 2^6 assignments fit in one uint64_t.

// A cut is an ordered set of node IDs. Unused array entries stay zero, but
// equality and hashing inspect only the first nLeaves entries.
struct LsvCut {
  int nLeaves = 0;
  int leaves[kMaxLeaves] = {};
};

struct CutEqual {
  bool operator()(const LsvCut& a, const LsvCut& b) const {
    if (a.nLeaves != b.nLeaves) return false;
    for (int j = 0; j < a.nLeaves; ++j)
      if (a.leaves[j] != b.leaves[j]) return false;
    return true;
  }
};

struct CutHash {
  size_t operator()(const LsvCut& cut) const {
    size_t hash = static_cast<size_t>(cut.nLeaves);
    for (int j = 0; j < cut.nLeaves; ++j)
      hash = hash * 131 + static_cast<size_t>(cut.leaves[j]);
    return hash;
  }
};

LsvCut TrivialCut(int id) {
  LsvCut cut;
  cut.nLeaves = 1;
  cut.leaves[0] = id;
  return cut;
}

// Merge two sorted leaf sets, inserting a shared leaf only once. The operation
// stops as soon as the union would exceed k; it never writes past the array.
bool MergeCuts(const LsvCut& a, const LsvCut& b, int k, LsvCut& out) {
  int i = 0, j = 0;
  out.nLeaves = 0;
  while (i < a.nLeaves || j < b.nLeaves) {
    int id;
    if (j == b.nLeaves || (i < a.nLeaves && a.leaves[i] < b.leaves[j])) {
      id = a.leaves[i++];
    } else if (i == a.nLeaves || b.leaves[j] < a.leaves[i]) {
      id = b.leaves[j++];
    } else {
      id = a.leaves[i++];
      ++j;
    }
    if (out.nLeaves == k) return false;
    out.leaves[out.nLeaves++] = id;
  }
  return true;
}

// Build a fanin-before-root order ourselves. A valid strashed network can have
// fanins with larger IDs after rewriting, so numeric ID order is insufficient.
// The explicit stack also avoids recursion limits on deep AIGs.
bool BuildNodeOrder(Abc_Ntk_t* network, std::vector<Abc_Obj_t*>& order) {
  std::vector<unsigned char> state(Abc_NtkObjNumMax(network), 0);
  state[Abc_ObjId(Abc_AigConst1(network))] = 2;
  Abc_Obj_t* obj;
  int i;
  // A latch output is also a combinational input: cut computation does not
  // follow the feedback path through a latch into the previous time step.
  Abc_NtkForEachCi(network, obj, i) state[Abc_ObjId(obj)] = 2;
  Abc_NtkForEachNode(network, obj, i) {
    if (Abc_ObjFaninNum(obj) != 2) {
      Abc_Print(-1, "Node %d is not a two-input AIG AND node.\n", Abc_ObjId(obj));
      return false;
    }
  }

  std::vector<Abc_Obj_t*> stack;
  Abc_NtkForEachNode(network, obj, i) {
    stack.push_back(obj);
    while (!stack.empty()) {
      Abc_Obj_t* node = stack.back();
      int id = Abc_ObjId(node);
      if (state[id] == 2) {
        stack.pop_back();
        continue;
      }
      if (!Abc_ObjIsNode(node) || Abc_ObjFaninNum(node) != 2) {
        Abc_Print(-1, "Unsupported AIG object %d.\n", id);
        return false;
      }
      state[id] = 1;  // Active on this DFS path; seeing it as a child is a cycle.
      bool descend = false;
      for (int edge = 0; edge < 2; ++edge) {
        Abc_Obj_t* child = Abc_ObjFanin(node, edge);
        int childId = Abc_ObjId(child);
        if (state[childId] == 1) {
          Abc_Print(-1, "The AIG contains a combinational cycle at node %d.\n", childId);
          return false;
        }
        if (state[childId] == 0) {
          stack.push_back(child);
          descend = true;
          break;
        }
      }
      if (!descend) {
        order.push_back(node);
        state[id] = 2;
        stack.pop_back();
      }
    }
  }
  return true;
}

using CutVisitor = bool (*)(Abc_Obj_t*, const std::vector<LsvCut>&, void*);

// Recurrence:
//   cuts(input) = {{input}}, cuts(constant 1) = {empty set}
//   cuts(node) = {{node}} union {a union b: a,b are fanin cuts, |a union b| <= k}
// Only exact duplicates are discarded. Dropping supersets would omit cuts
// requested by "all k-feasible cuts", especially in reconvergent networks.
int EnumerateCuts(Abc_Ntk_t* network, int k, CutVisitor visit, void* user) {
  std::vector<Abc_Obj_t*> order;
  if (!BuildNodeOrder(network, order)) return 1;
  int nObjects = Abc_NtkObjNumMax(network);
  std::vector<std::vector<LsvCut>> cuts(nObjects);
  std::vector<int> remainingUses(nObjects, 0);
  cuts[Abc_ObjId(Abc_AigConst1(network))].push_back(LsvCut());
  Abc_Obj_t* obj;
  int i;
  Abc_NtkForEachCi(network, obj, i)
    cuts[Abc_ObjId(obj)].push_back(TrivialCut(Abc_ObjId(obj)));

  for (Abc_Obj_t* node : order) {
    ++remainingUses[Abc_ObjFaninId0(node)];
    ++remainingUses[Abc_ObjFaninId1(node)];
  }
  for (Abc_Obj_t* node : order) {
    int id = Abc_ObjId(node);
    int id0 = Abc_ObjFaninId0(node), id1 = Abc_ObjFaninId1(node);
    std::vector<LsvCut>& mine = cuts[id];
    std::unordered_set<LsvCut, CutHash, CutEqual> seen;
    mine.push_back(TrivialCut(id));
    seen.insert(mine.back());
    LsvCut merged;
    for (const LsvCut& a : cuts[id0])
      for (const LsvCut& b : cuts[id1])
        if (MergeCuts(a, b, k, merged) && seen.insert(merged).second)
          mine.push_back(merged);
    if (!visit(node, mine, user)) return 1;

    // A fanin's cut set is needed only until its last AND fanout is processed.
    // Truth-table/BDD evaluation reads the AIG itself, not these cached sets.
    if (--remainingUses[id0] == 0) std::vector<LsvCut>().swap(cuts[id0]);
    if (--remainingUses[id1] == 0) std::vector<LsvCut>().swap(cuts[id1]);
    if (remainingUses[id] == 0) std::vector<LsvCut>().swap(mine);
  }
  return 0;
}

// Variable at binary digit d of an assignment counter. A cut's smallest ID is
// the first input, hence its MOST significant digit, as in the PDF's 0x4 example.
constexpr uint64_t kVariableTables[kMaxLeaves] = {
    0xAAAAAAAAAAAAAAAAULL, 0xCCCCCCCCCCCCCCCCULL, 0xF0F0F0F0F0F0F0F0ULL,
    0xFF00FF00FF00FF00ULL, 0xFFFF0000FFFF0000ULL, 0xFFFFFFFF00000000ULL};

uint64_t TruthMask(int nLeaves) {
  // Shifting by 64 is undefined in C++; handle a six-input table separately.
  return nLeaves == kMaxLeaves ? ~uint64_t(0)
                             : (uint64_t(1) << (1U << nLeaves)) - 1;
}

// Leaves are preloaded into values and act as independent inputs. The walk
// must stop there, even if a leaf is itself an AND node or its fanins appear
// elsewhere in the cut. Re-evaluating that leaf would change the cut function.
bool EvaluateTruthTable(Abc_Obj_t* root, const LsvCut& cut, uint64_t& table) {
  std::unordered_map<int, uint64_t> values;
  for (int j = 0; j < cut.nLeaves; ++j)
    values[cut.leaves[j]] = kVariableTables[cut.nLeaves - 1 - j];
  std::vector<Abc_Obj_t*> stack(1, root);
  while (!stack.empty()) {
    Abc_Obj_t* node = stack.back();
    int id = Abc_ObjId(node);
    if (values.find(id) != values.end()) {
      stack.pop_back();
    } else if (Abc_AigNodeIsConst(node)) {
      values[id] = ~uint64_t(0);
      stack.pop_back();
    } else {
      if (!Abc_ObjIsNode(node) || Abc_ObjFaninNum(node) != 2) {
        Abc_Print(-1, "Cut at node %d does not cover input %d.\n", Abc_ObjId(root), id);
        return false;
      }
      auto f0 = values.find(Abc_ObjFaninId0(node));
      if (f0 == values.end()) {
        stack.push_back(Abc_ObjFanin0(node));
        continue;
      }
      auto f1 = values.find(Abc_ObjFaninId1(node));
      if (f1 == values.end()) {
        stack.push_back(Abc_ObjFanin1(node));
        continue;
      }
      uint64_t a = Abc_ObjFaninC0(node) ? ~f0->second : f0->second;
      uint64_t b = Abc_ObjFaninC1(node) ? ~f1->second : f1->second;
      values[id] = a & b;
      stack.pop_back();
    }
  }
  table = values.at(Abc_ObjId(root)) & TruthMask(cut.nLeaves);
  return true;
}

// Construct a BDD directly from the cut cone with general CUDD AND operations.
// Every value in the map owns one reference, including complemented pointers;
// CUDD's reference operations regularize these pointers internally.
bool EvaluateBddSize(DdManager* manager, Abc_Obj_t* root, const LsvCut& cut,
                     int& size) {
  std::unordered_map<int, DdNode*> values;
  bool success = true;
  for (int j = 0; j < cut.nLeaves; ++j) {
    DdNode* variable = Cudd_bddIthVar(manager, j);
    if (!variable) {
      success = false;
      break;
    }
    Cudd_Ref(variable);
    values[cut.leaves[j]] = variable;
  }
  std::vector<Abc_Obj_t*> stack(1, root);
  while (success && !stack.empty()) {
    Abc_Obj_t* node = stack.back();
    int id = Abc_ObjId(node);
    if (values.find(id) != values.end()) {
      stack.pop_back();
      continue;
    }
    DdNode* value;
    if (Abc_AigNodeIsConst(node)) {
      value = Cudd_ReadOne(manager);
    } else {
      if (!Abc_ObjIsNode(node) || Abc_ObjFaninNum(node) != 2) {
        Abc_Print(-1, "Cut at node %d does not cover input %d.\n", Abc_ObjId(root), id);
        success = false;
        break;
      }
      auto f0 = values.find(Abc_ObjFaninId0(node));
      if (f0 == values.end()) {
        stack.push_back(Abc_ObjFanin0(node));
        continue;
      }
      auto f1 = values.find(Abc_ObjFaninId1(node));
      if (f1 == values.end()) {
        stack.push_back(Abc_ObjFanin1(node));
        continue;
      }
      DdNode* a = Cudd_NotCond(f0->second, Abc_ObjFaninC0(node));
      DdNode* b = Cudd_NotCond(f1->second, Abc_ObjFaninC1(node));
      value = Cudd_bddAnd(manager, a, b);
    }
    if (!value) {
      success = false;
      break;
    }
    Cudd_Ref(value);  // Protect this result before another CUDD operation.
    values[id] = value;
    stack.pop_back();
  }
  if (success) size = Cudd_DagSize(values.at(Abc_ObjId(root)));
  // Release on both success and failure, so a failed operation cannot leak
  // intermediate BDDs. Several AIG nodes can refer to the same BDD: each map
  // entry still contributes exactly one matching Ref/RecursiveDeref pair.
  for (const auto& entry : values) Cudd_RecursiveDeref(manager, entry.second);
  if (!success) Abc_Print(-1, "Could not construct the cut BDD at node %d.\n", Abc_ObjId(root));
  return success;
}

void PrintPrefix(Abc_Obj_t* node, const LsvCut& cut) {
  std::printf("%d:", Abc_ObjId(node));
  for (int j = 0; j < cut.nLeaves; ++j) std::printf(" %d", cut.leaves[j]);
  std::printf(": ");
}

bool PrintTruthTables(Abc_Obj_t* node, const std::vector<LsvCut>& cuts, void*) {
  for (const LsvCut& cut : cuts) {
    uint64_t table;
    if (!EvaluateTruthTable(node, cut, table)) return false;
    PrintPrefix(node, cut);
    std::printf("%llX\n", static_cast<unsigned long long>(table));
  }
  return true;
}

bool PrintBddSizes(Abc_Obj_t* node, const std::vector<LsvCut>& cuts, void* user) {
  DdManager* manager = static_cast<DdManager*>(user);
  for (const LsvCut& cut : cuts) {
    int size;
    if (!EvaluateBddSize(manager, node, cut, size)) return false;
    PrintPrefix(node, cut);
    std::printf("%d\n", size);
  }
  return true;
}

// Return a positive k, zero after a network error, or -1 to print usage.
int ParseArguments(Abc_Frame_t* frame, int argc, char** argv, Abc_Ntk_t*& network) {
  Extra_UtilGetoptReset();
  if (Extra_UtilGetopt(argc, argv, "h") != EOF) return -1;
  if (globalUtilOptind + 1 != argc) return -1;
  const char* argument = argv[globalUtilOptind];
  char* end = nullptr;
  errno = 0;
  long k = std::strtol(argument, &end, 10);
  if (end == argument || *end != '\0' || errno == ERANGE || k < 1 || k > kMaxLeaves) {
    Abc_Print(-1, "k must be an integer between 1 and %d.\n", kMaxLeaves);
    return -1;
  }
  network = Abc_FrameReadNtk(frame);
  if (!network) {
    Abc_Print(-1, "Empty network.\n");
    return 0;
  }
  if (!Abc_NtkIsStrash(network)) {
    Abc_Print(-1, "The network is not a strashed AIG; run \"strash\" first.\n");
    return 0;
  }
  return static_cast<int>(k);
}

void PrintUsage(const char* name, const char* result) {
  Abc_Print(-2, "usage: %s [-h] <k>\n", name);
  Abc_Print(-2, "\tprints all unique k-feasible cuts of each AND node and %s\n", result);
  Abc_Print(-2, "\t<k> : maximum number of leaves, 1 <= k <= %d (PA tests use 2..6)\n", kMaxLeaves);
  Abc_Print(-2, "\t-h  : print this usage\n");
}

}  // namespace

int Lsv_CommandCutTt(Abc_Frame_t* frame, int argc, char** argv) {
  Abc_Ntk_t* network = nullptr;
  int k = ParseArguments(frame, argc, argv, network);
  if (k < 0) PrintUsage("lsv_cut_tt", "its hexadecimal truth table");
  if (k <= 0) return 1;
  return EnumerateCuts(network, k, PrintTruthTables, nullptr);
}

int Lsv_CommandCutBddSize(Abc_Frame_t* frame, int argc, char** argv) {
  Abc_Ntk_t* network = nullptr;
  int k = ParseArguments(frame, argc, argv, network);
  if (k < 0) PrintUsage("lsv_cut_bddsize", "its ROBDD size");
  if (k <= 0) return 1;
  DdManager* manager = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  if (!manager) {
    Abc_Print(-1, "Could not allocate a CUDD manager.\n");
    return 1;
  }
  // Leaf j is variable j, in ascending node-ID order. Disable automatic
  // reordering explicitly: a different order can change the required size.
  Cudd_AutodynDisable(manager);
  int result = EnumerateCuts(network, k, PrintBddSizes, manager);
  if (Cudd_CheckZeroRef(manager) != 0) {
    Abc_Print(-1, "Unreleased temporary BDD references.\n");
    result = 1;
  }
  Cudd_Quit(manager);
  return result;
}
