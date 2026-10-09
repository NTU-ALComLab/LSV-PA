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

// Only the first leafCount entries are used, in ascending node-ID order.
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

// Sorted set union; return false if the result would exceed maxLeaves.
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
      nextLeafId = left.leaves[leftIndex++];
      ++rightIndex;
    }
    if (merged.leafCount == maxLeaves) return false;
    merged.leaves[merged.leafCount++] = nextLeafId;
  }
  return true;
}

enum class DfsState : unsigned char { NotVisited, OnStack, Ready };

// Node IDs need not be topological after rewriting. Use an iterative DFS.
bool BuildTopologicalOrder(Abc_Ntk_t* network, std::vector<Abc_Obj_t*>& order) {
  std::vector<DfsState> state(Abc_NtkObjNumMax(network), DfsState::NotVisited);
  state[Abc_ObjId(Abc_AigConst1(network))] = DfsState::Ready;
  Abc_Obj_t* obj;
  int i;
  // Latch outputs are boundaries, just like primary inputs.
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

using CutPrinter = bool (*)(Abc_Obj_t*, const CutList&, DdManager*);

void ReleaseCutList(CutList& cuts) {
  // clear() retains capacity; swapping with an empty list frees it.
  CutList empty;
  cuts.swap(empty);
}

//   cuts(input) = {{input}}, cuts(constant 1) = {empty set}
//   cuts(node) = {{node}} union {a union b: a,b are fanin cuts, |a union b| <= k}
// Keep distinct supersets produced by reconvergence; remove only duplicates.
int EnumerateCuts(Abc_Ntk_t* network, int maxLeaves, CutPrinter printCuts,
                  DdManager* bddManager) {
  std::vector<Abc_Obj_t*> order;
  if (!BuildTopologicalOrder(network, order)) return 1;
  int objectCount = Abc_NtkObjNumMax(network);
  std::vector<CutList> cutsByNode(objectCount);
  std::vector<int> remainingFanouts(objectCount, 0);

  // Constant 1 has no input variables, hence its empty cut.
  cutsByNode[Abc_ObjId(Abc_AigConst1(network))].push_back(LsvCut());
  Abc_Obj_t* obj;
  int i;
  Abc_NtkForEachCi(network, obj, i)
    cutsByNode[Abc_ObjId(obj)].push_back(MakeUnitCut(Abc_ObjId(obj)));

  // Count remaining uses of each cut list by AND fanin edges.
  for (Abc_Obj_t* node : order) {
    ++remainingFanouts[Abc_ObjFaninId0(node)];
    ++remainingFanouts[Abc_ObjFaninId1(node)];
  }
  for (Abc_Obj_t* node : order) {
    int nodeId = Abc_ObjId(node);
    int fanin0Id = Abc_ObjFaninId0(node), fanin1Id = Abc_ObjFaninId1(node);
    CutList& nodeCuts = cutsByNode[nodeId];
    CutSet seen;

    AddCutIfNew(MakeUnitCut(nodeId), nodeCuts, seen);

    LsvCut merged;
    for (const LsvCut& leftCut : cutsByNode[fanin0Id]) {
      for (const LsvCut& rightCut : cutsByNode[fanin1Id]) {
        if (MergeCuts(leftCut, rightCut, maxLeaves, merged))
          AddCutIfNew(merged, nodeCuts, seen);
      }
    }

    if (!printCuts(node, nodeCuts, bddManager)) return 1;

    // Free cut lists after their last use. Evaluation reads the AIG itself.
    for (int edge = 0; edge < 2; ++edge) {
      int faninId = Abc_ObjFaninId(node, edge);
      --remainingFanouts[faninId];
      if (remainingFanouts[faninId] == 0) ReleaseCutList(cutsByNode[faninId]);
    }
    if (remainingFanouts[nodeId] == 0) ReleaseCutList(nodeCuts);
  }
  return 0;
}

// Table bit i contains binary digit d of assignment index i.
constexpr uint64_t kVariableTruthTables[kMaxCutLeaves] = {
    0xAAAAAAAAAAAAAAAAULL,  // d=0: blocks of 1 zero, then 1 one.
    0xCCCCCCCCCCCCCCCCULL,  // d=1: blocks of 2 zeros, then 2 ones.
    0xF0F0F0F0F0F0F0F0ULL,  // d=2: blocks of 4.
    0xFF00FF00FF00FF00ULL,  // d=3: blocks of 8.
    0xFFFF0000FFFF0000ULL,  // d=4: blocks of 16.
    0xFFFFFFFF00000000ULL}; // d=5: blocks of 32.

uint64_t TruthMask(int leafCount) {
  // Avoid shifting by 64 for a six-leaf cut.
  if (leafCount == kMaxCutLeaves) return ~uint64_t(0);
  unsigned assignmentCount = 1U << leafCount;
  return (uint64_t(1) << assignmentCount) - 1;
}

// Treat leaves as independent inputs, even when they are internal AND nodes.
bool EvaluateTruthTable(Abc_Obj_t* root, const LsvCut& cut, uint64_t& table) {
  std::unordered_map<int, uint64_t> truthByNode;

  // The smallest leaf ID uses the most significant assignment digit.
  for (int leafIndex = 0; leafIndex < cut.leafCount; ++leafIndex) {
    int assignmentDigit = cut.leafCount - 1 - leafIndex;
    truthByNode[cut.leaves[leafIndex]] = kVariableTruthTables[assignmentDigit];
  }

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
      uint64_t fanin0Table = fanin0Entry->second;
      uint64_t fanin1Table = fanin1Entry->second;
      if (Abc_ObjFaninC0(node)) fanin0Table = ~fanin0Table;
      if (Abc_ObjFaninC1(node)) fanin1Table = ~fanin1Table;
      truthByNode[nodeId] = fanin0Table & fanin1Table;
      pendingNodes.pop_back();
    }
  }
  table = truthByNode.at(Abc_ObjId(root)) & TruthMask(cut.leafCount);
  return true;
}

// Same cone evaluation as above, with one CUDD reference per cached value.
bool EvaluateBddSize(DdManager* manager, Abc_Obj_t* root, const LsvCut& cut,
                     int& size) {
  std::unordered_map<int, DdNode*> bddByNode;
  bool success = true;

  // Variable 0 corresponds to the smallest leaf ID.
  for (int leafIndex = 0; leafIndex < cut.leafCount; ++leafIndex) {
    DdNode* variable = Cudd_bddIthVar(manager, leafIndex);
    if (!variable) {
      success = false;
      break;
    }
    Cudd_Ref(variable);
    bddByNode[cut.leaves[leafIndex]] = variable;
  }

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
      DdNode* fanin0Bdd = Cudd_NotCond(fanin0Entry->second, Abc_ObjFaninC0(node));
      DdNode* fanin1Bdd = Cudd_NotCond(fanin1Entry->second, Abc_ObjFaninC1(node));
      nodeBdd = Cudd_bddAnd(manager, fanin0Bdd, fanin1Bdd);
    }
    if (!nodeBdd) {
      success = false;
      break;
    }
    Cudd_Ref(nodeBdd);  // Keep it alive across later CUDD operations.
    bddByNode[nodeId] = nodeBdd;
    pendingNodes.pop_back();
  }
  if (success) size = Cudd_DagSize(bddByNode.at(Abc_ObjId(root)));
  // Release once per entry, including shared BDDs and failure paths.
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
  // Keep ascending leaf-ID order; reordering can change the BDD size.
  Cudd_AutodynDisable(manager);
  int result = EnumerateCuts(network, k, PrintBddSizes, manager);
  if (Cudd_CheckZeroRef(manager) != 0) {
    Abc_Print(-1, "Unreleased temporary BDD references.\n");
    result = 1;
  }
  Cudd_Quit(manager);
  return result;
}
