/**
 * PA1 Exercise 4: enumerate k-feasible cuts and evaluate their functions.
 *
 * All cut-specific data structures and algorithms below are implemented here.
 * ABC supplies only network accessors; CUDD supplies general BDD operations.
 * No ABC cut-enumeration, cut truth-table, or cut-BDD helpers are used.
 *
 * Suggested reading order:
 *   command entry points at the bottom -> ParseArguments -> EnumerateCuts
 *   -> MergeCuts -> EvaluateTruthTable / EvaluateBddSize -> output printers.
 * README_lsvCut.md walks through the same flow with the supplied example.
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

constexpr int kMaxCutLeaves = 6;  // 2^6 assignments fit in one uint64_t.

// A cut lists the boundary nodes where we stop walking toward the inputs.
// Only leaves[0..leafCount-1] are meaningful, always in ascending ID order.
// Example: leafCount = 2, leaves = {1, 2, ...} represents the cut {1, 2}.
struct LsvCut {
  int leafCount = 0;
  int leaves[kMaxCutLeaves] = {};
};

using CutList = std::vector<LsvCut>;

struct CutEqual {
  bool operator()(const LsvCut& a, const LsvCut& b) const {
    if (a.leafCount != b.leafCount) return false;
    for (int j = 0; j < a.leafCount; ++j)
      if (a.leaves[j] != b.leaves[j]) return false;
    return true;
  }
};

struct CutHash {
  size_t operator()(const LsvCut& cut) const {
    size_t hash = static_cast<size_t>(cut.leafCount);
    for (int j = 0; j < cut.leafCount; ++j)
      hash = hash * 131 + static_cast<size_t>(cut.leaves[j]);
    return hash;
  }
};

using CutSet = std::unordered_set<LsvCut, CutHash, CutEqual>;

// The hash helps find candidates quickly; CutEqual still checks the complete
// leaf set, so two cuts with the same hash cannot be mistaken for each other.
void AddCutIfNew(const LsvCut& candidate, CutList& output, CutSet& seen) {
  bool inserted = seen.insert(candidate).second;
  if (inserted) output.push_back(candidate);
}

LsvCut MakeUnitCut(int id) {
  LsvCut cut;
  cut.leafCount = 1;
  cut.leaves[0] = id;
  return cut;
}

// Merge two sorted leaf sets, inserting a shared leaf only once. The operation
// stops as soon as the union would exceed k; it never writes past the array.
bool MergeCuts(const LsvCut& left, const LsvCut& right, int maxLeaves,
               LsvCut& merged) {
  int leftIndex = 0, rightIndex = 0;
  merged.leafCount = 0;
  while (leftIndex < left.leafCount || rightIndex < right.leafCount) {
    int nextLeafId;
    if (rightIndex == right.leafCount ||
        (leftIndex < left.leafCount && left.leaves[leftIndex] < right.leaves[rightIndex])) {
      nextLeafId = left.leaves[leftIndex++];
    } else if (leftIndex == left.leafCount ||
               right.leaves[rightIndex] < left.leaves[leftIndex]) {
      nextLeafId = right.leaves[rightIndex++];
    } else {
      // The same leaf occurs in both cuts. Add it once and advance both lists.
      nextLeafId = left.leaves[leftIndex++];
      ++rightIndex;
    }
    if (merged.leafCount == maxLeaves) return false;
    merged.leaves[merged.leafCount++] = nextLeafId;
  }
  return true;
}

enum class DfsState : unsigned char { NotVisited, OnStack, Ready };

// Build a fanin-before-root order ourselves. A valid strashed network can have
// fanins with larger IDs after rewriting, so numeric ID order is insufficient.
// The explicit stack also avoids recursion limits on deep AIGs.
bool BuildTopologicalOrder(Abc_Ntk_t* network, std::vector<Abc_Obj_t*>& order) {
  std::vector<DfsState> state(Abc_NtkObjNumMax(network), DfsState::NotVisited);
  state[Abc_ObjId(Abc_AigConst1(network))] = DfsState::Ready;
  Abc_Obj_t* obj;
  int i;
  // A latch output is also a combinational input: cut computation does not
  // follow the feedback path through a latch into the previous time step.
  Abc_NtkForEachCi(network, obj, i) state[Abc_ObjId(obj)] = DfsState::Ready;
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
      if (state[id] == DfsState::Ready) {
        stack.pop_back();
        continue;
      }
      if (!Abc_ObjIsNode(node) || Abc_ObjFaninNum(node) != 2) {
        Abc_Print(-1, "Unsupported AIG object %d.\n", id);
        return false;
      }
      // A node stays OnStack until both its fanins are Ready.
      state[id] = DfsState::OnStack;
      bool descend = false;
      for (int edge = 0; edge < 2; ++edge) {
        Abc_Obj_t* child = Abc_ObjFanin(node, edge);
        int childId = Abc_ObjId(child);
        if (state[childId] == DfsState::OnStack) {
          Abc_Print(-1, "The AIG contains a combinational cycle at node %d.\n", childId);
          return false;
        }
        if (state[childId] == DfsState::NotVisited) {
          stack.push_back(child);
          descend = true;
          break;
        }
      }
      if (!descend) {
        order.push_back(node);
        state[id] = DfsState::Ready;
        stack.pop_back();
      }
    }
  }
  return true;
}

// A printer is a function we call after finding one node's complete cut list.
// The truth-table printer ignores the manager; the BDD printer uses it.
using CutPrinter = bool (*)(Abc_Obj_t*, const CutList&, DdManager*);

void ReleaseCutList(CutList& cuts) {
  // clear() would retain the vector's allocation. Swapping with an empty list
  // releases that memory when the local empty list goes out of scope.
  CutList empty;
  cuts.swap(empty);
}

// Recurrence:
//   cuts(input) = {{input}}, cuts(constant 1) = {empty set}
//   cuts(node) = {{node}} union {a union b: a,b are fanin cuts, |a union b| <= k}
// Only exact duplicates are discarded. Dropping supersets would omit cuts
// requested by "all k-feasible cuts", especially in reconvergent networks.
int EnumerateCuts(Abc_Ntk_t* network, int maxLeaves, CutPrinter printCuts,
                  DdManager* bddManager) {
  // Step 1: prepare a fanin-before-root order for the bottom-up recurrence.
  std::vector<Abc_Obj_t*> order;
  if (!BuildTopologicalOrder(network, order)) return 1;
  int objectCount = Abc_NtkObjNumMax(network);
  // cutsByNode[id] is the list of cuts for that node, not one individual cut.
  std::vector<CutList> cutsByNode(objectCount);
  std::vector<int> remainingFanouts(objectCount, 0);

  // Step 2: seed the boundaries. An input has its unit cut; constant 1 needs
  // no input variables, hence its empty cut.
  cutsByNode[Abc_ObjId(Abc_AigConst1(network))].push_back(LsvCut());
  Abc_Obj_t* obj;
  int i;
  Abc_NtkForEachCi(network, obj, i)
    cutsByNode[Abc_ObjId(obj)].push_back(MakeUnitCut(Abc_ObjId(obj)));

  // Count how many future AND nodes still need each cached cut list.
  for (Abc_Obj_t* node : order) {
    ++remainingFanouts[Abc_ObjFaninId0(node)];
    ++remainingFanouts[Abc_ObjFaninId1(node)];
  }
  for (Abc_Obj_t* node : order) {
    int nodeId = Abc_ObjId(node);
    int fanin0Id = Abc_ObjFaninId0(node), fanin1Id = Abc_ObjFaninId1(node);
    CutList& nodeCuts = cutsByNode[nodeId];
    CutSet seen;

    // Step 3: the root itself is a valid one-leaf boundary.
    AddCutIfNew(MakeUnitCut(nodeId), nodeCuts, seen);

    // Step 4: try every pair of fanin cuts, keeping each feasible union once.
    LsvCut merged;
    for (const LsvCut& leftCut : cutsByNode[fanin0Id]) {
      for (const LsvCut& rightCut : cutsByNode[fanin1Id]) {
        if (MergeCuts(leftCut, rightCut, maxLeaves, merged))
          AddCutIfNew(merged, nodeCuts, seen);
      }
    }

    // Step 5: the same enumeration feeds either truth-table or BDD output.
    if (!printCuts(node, nodeCuts, bddManager)) return 1;

    // A fanin's cut set is needed only until its last AND fanout is processed.
    // Truth-table/BDD evaluation reads the AIG itself, not these cached sets.
    for (int edge = 0; edge < 2; ++edge) {
      int faninId = Abc_ObjFaninId(node, edge);
      --remainingFanouts[faninId];
      if (remainingFanouts[faninId] == 0) ReleaseCutList(cutsByNode[faninId]);
    }
    if (remainingFanouts[nodeId] == 0) ReleaseCutList(nodeCuts);
  }
  return 0;
}

// Variable at binary digit d of an assignment counter. A cut's smallest ID is
// the first input, hence its MOST significant digit, as in the PDF's 0x4 example.
constexpr uint64_t kVariableTruthTables[kMaxCutLeaves] = {
    0xAAAAAAAAAAAAAAAAULL,  // Digit 0: alternates 0,1 every assignment.
    0xCCCCCCCCCCCCCCCCULL,  // Digit 1: alternates 0,0,1,1.
    0xF0F0F0F0F0F0F0F0ULL,  // Digit 2: four zeros, then four ones.
    0xFF00FF00FF00FF00ULL,  // Digit 3: eight zeros, then eight ones.
    0xFFFF0000FFFF0000ULL,  // Digit 4: sixteen zeros, then sixteen ones.
    0xFFFFFFFF00000000ULL}; // Digit 5: thirty-two zeros, then thirty-two ones.

uint64_t TruthMask(int leafCount) {
  // Shifting by 64 is undefined in C++; handle a six-input table separately.
  if (leafCount == kMaxCutLeaves) return ~uint64_t(0);
  unsigned assignmentCount = 1U << leafCount;
  return (uint64_t(1) << assignmentCount) - 1;
}

// Leaves are preloaded into values and act as independent inputs. The walk
// must stop there, even if a leaf is itself an AND node or its fanins appear
// elsewhere in the cut. Re-evaluating that leaf would change the cut function.
bool EvaluateTruthTable(Abc_Obj_t* root, const LsvCut& cut, uint64_t& table) {
  std::unordered_map<int, uint64_t> truthByNode;

  // Step 1: assign one independent variable to each leaf. For {1,2}, the
  // low four bits are leaf 1 = 1100 and leaf 2 = 1010 (MSB printed first).
  for (int leafIndex = 0; leafIndex < cut.leafCount; ++leafIndex) {
    int assignmentDigit = cut.leafCount - 1 - leafIndex;
    truthByNode[cut.leaves[leafIndex]] = kVariableTruthTables[assignmentDigit];
  }

  // Step 2: revisit a pending node until both fanins have cached values.
  // Preloaded leaves already have values, so their own fanins are never read.
  std::vector<Abc_Obj_t*> pendingNodes(1, root);
  while (!pendingNodes.empty()) {
    Abc_Obj_t* node = pendingNodes.back();
    int nodeId = Abc_ObjId(node);
    if (truthByNode.find(nodeId) != truthByNode.end()) {
      pendingNodes.pop_back();
    } else if (Abc_AigNodeIsConst(node)) {
      truthByNode[nodeId] = ~uint64_t(0);
      pendingNodes.pop_back();
    } else {
      if (!Abc_ObjIsNode(node) || Abc_ObjFaninNum(node) != 2) {
        Abc_Print(-1, "Cut at node %d does not cover input %d.\n", Abc_ObjId(root), nodeId);
        return false;
      }
      auto fanin0Entry = truthByNode.find(Abc_ObjFaninId0(node));
      if (fanin0Entry == truthByNode.end()) {
        pendingNodes.push_back(Abc_ObjFanin0(node));
        continue;
      }
      auto fanin1Entry = truthByNode.find(Abc_ObjFaninId1(node));
      if (fanin1Entry == truthByNode.end()) {
        pendingNodes.push_back(Abc_ObjFanin1(node));
        continue;
      }
      // Step 3: an inverted edge negates its fanin's function before the AND.
      // mapEntry->second is the cached value; its first field is the node ID.
      uint64_t fanin0Table = fanin0Entry->second;
      uint64_t fanin1Table = fanin1Entry->second;
      if (Abc_ObjFaninC0(node)) fanin0Table = ~fanin0Table;
      if (Abc_ObjFaninC1(node)) fanin1Table = ~fanin1Table;
      truthByNode[nodeId] = fanin0Table & fanin1Table;
      pendingNodes.pop_back();
    }
  }
  // Step 4: keep only the 2^leafCount assignments that belong to this cut.
  table = truthByNode.at(Abc_ObjId(root)) & TruthMask(cut.leafCount);
  return true;
}

// Construct a BDD directly from the cut cone with general CUDD AND operations.
// Every value in the map owns one reference, including complemented pointers;
// CUDD's reference operations regularize these pointers internally.
bool EvaluateBddSize(DdManager* manager, Abc_Obj_t* root, const LsvCut& cut,
                     int& size) {
  std::unordered_map<int, DdNode*> bddByNode;
  bool success = true;

  // Step 1: use the same sorted leaves as the truth-table command. Variable
  // index 0 tests the smallest leaf ID first; variable index 1 tests the next.
  for (int leafIndex = 0; leafIndex < cut.leafCount; ++leafIndex) {
    DdNode* variable = Cudd_bddIthVar(manager, leafIndex);
    if (!variable) {
      success = false;
      break;
    }
    Cudd_Ref(variable);
    bddByNode[cut.leaves[leafIndex]] = variable;
  }

  // Step 2: the cone walk matches EvaluateTruthTable; cached values are now
  // BDD pointers rather than 64-bit words. A cached leaf still stops the walk.
  std::vector<Abc_Obj_t*> pendingNodes(1, root);
  while (success && !pendingNodes.empty()) {
    Abc_Obj_t* node = pendingNodes.back();
    int nodeId = Abc_ObjId(node);
    if (bddByNode.find(nodeId) != bddByNode.end()) {
      pendingNodes.pop_back();
      continue;
    }
    DdNode* nodeBdd;
    if (Abc_AigNodeIsConst(node)) {
      nodeBdd = Cudd_ReadOne(manager);
    } else {
      if (!Abc_ObjIsNode(node) || Abc_ObjFaninNum(node) != 2) {
        Abc_Print(-1, "Cut at node %d does not cover input %d.\n", Abc_ObjId(root), nodeId);
        success = false;
        break;
      }
      auto fanin0Entry = bddByNode.find(Abc_ObjFaninId0(node));
      if (fanin0Entry == bddByNode.end()) {
        pendingNodes.push_back(Abc_ObjFanin0(node));
        continue;
      }
      auto fanin1Entry = bddByNode.find(Abc_ObjFaninId1(node));
      if (fanin1Entry == bddByNode.end()) {
        pendingNodes.push_back(Abc_ObjFanin1(node));
        continue;
      }
      // Step 3: Cudd_NotCond applies an edge's complement flag, and bddAnd
      // combines the two fanin functions into this node's reduced BDD.
      DdNode* fanin0Bdd = Cudd_NotCond(fanin0Entry->second, Abc_ObjFaninC0(node));
      DdNode* fanin1Bdd = Cudd_NotCond(fanin1Entry->second, Abc_ObjFaninC1(node));
      nodeBdd = Cudd_bddAnd(manager, fanin0Bdd, fanin1Bdd);
    }
    if (!nodeBdd) {
      success = false;
      break;
    }
    Cudd_Ref(nodeBdd);  // Protect this result before another CUDD operation.
    bddByNode[nodeId] = nodeBdd;
    pendingNodes.pop_back();
  }
  // Step 4: measure before releasing the references that keep the BDD alive.
  if (success) size = Cudd_DagSize(bddByNode.at(Abc_ObjId(root)));
  // Release on both success and failure, so a failed operation cannot leak
  // intermediate BDDs. Several AIG nodes can refer to the same BDD: each map
  // entry still contributes exactly one matching Ref/RecursiveDeref pair.
  for (const auto& entry : bddByNode) Cudd_RecursiveDeref(manager, entry.second);
  if (!success) Abc_Print(-1, "Could not construct the cut BDD at node %d.\n", Abc_ObjId(root));
  return success;
}

void PrintPrefix(Abc_Obj_t* node, const LsvCut& cut) {
  std::printf("%d:", Abc_ObjId(node));
  for (int j = 0; j < cut.leafCount; ++j) std::printf(" %d", cut.leaves[j]);
  std::printf(": ");
}

bool PrintTruthTables(Abc_Obj_t* node, const CutList& cuts, DdManager*) {
  for (const LsvCut& cut : cuts) {
    uint64_t table;
    if (!EvaluateTruthTable(node, cut, table)) return false;
    PrintPrefix(node, cut);
    std::printf("%llX\n", static_cast<unsigned long long>(table));
  }
  return true;
}

bool PrintBddSizes(Abc_Obj_t* node, const CutList& cuts, DdManager* manager) {
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
  if (end == argument || *end != '\0' || errno == ERANGE || k < 1 || k > kMaxCutLeaves) {
    Abc_Print(-1, "k must be an integer between 1 and %d.\n", kMaxCutLeaves);
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
  Abc_Print(-2, "\t<k> : maximum number of leaves, 1 <= k <= %d (PA tests use 2..6)\n", kMaxCutLeaves);
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
