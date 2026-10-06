#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iterator>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

// Forward declarations
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBDDSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBDDSize, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

// ============================================================
// Phase 2: k-feasible Cut Enumeration (Bottom-up)
// ============================================================

static std::map<int, std::vector<std::vector<int>>> Lsv_NtkEnumerateCuts(
    Abc_Ntk_t* pNtk, int k) {
  std::map<int, std::vector<std::vector<int>>> nodeCuts;
  Abc_Obj_t* pObj;
  int i;

  // Step A-0: Initialize trivial cut for the constant-1 node.
  Abc_Obj_t* pConst1 = Abc_AigConst1(pNtk);
  if (pConst1) {
    int constId = Abc_ObjId(pConst1);
    nodeCuts[constId].push_back({constId});
  }

  // Step A-1: Initialize trivial cuts for all Primary Inputs.
  Abc_NtkForEachPi(pNtk, pObj, i) {
    int pid = Abc_ObjId(pObj);
    nodeCuts[pid].push_back({pid});
  }

  // Step B: Bottom-up merge for AND nodes.
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int nid = Abc_ObjId(pObj);
    Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pObj);
    int fid0 = Abc_ObjId(pFanin0);
    int fid1 = Abc_ObjId(pFanin1);

    std::set<std::vector<int>> cutSet;

    cutSet.insert({nid});

    const std::vector<std::vector<int>>& cuts0 = nodeCuts[fid0];
    const std::vector<std::vector<int>>& cuts1 = nodeCuts[fid1];
    // Pairwise merge
    for (const auto& c0 : cuts0) {
      for (const auto& c1 : cuts1) {

        std::vector<int> merged;
        merged.reserve(c0.size() + c1.size());
        std::set_union(c0.begin(), c0.end(), c1.begin(), c1.end(),
                       std::back_inserter(merged));

        // k-feasibility check
        if (static_cast<int>(merged.size()) <= k) {
          cutSet.insert(std::move(merged));
        }
      }
    }

    // Store 
    nodeCuts[nid].assign(cutSet.begin(), cutSet.end());
  }

  return nodeCuts;
}

// ============================================================
// Phase 3: Bitwise Parallel AIG Simulation for Truth Tables
// ============================================================

// Standard input patterns :
//   var 0: 0xAAAAAAAAAAAAAAAA  (...10101010)
//   var 1: 0xCCCCCCCCCCCCCCCC  (...11001100)
//   var 2: 0xF0F0F0F0F0F0F0F0  (...11110000)
static const uint64_t kInputPatterns[6] = {
    0xAAAAAAAAAAAAAAAAULL, 0xCCCCCCCCCCCCCCCCULL, 0xF0F0F0F0F0F0F0F0ULL,
    0xFF00FF00FF00FF00ULL, 0xFFFF0000FFFF0000ULL, 0xFFFFFFFF00000000ULL};

// Recursively simulates the AIG from 'nodeId' down to the cut leaves
static uint64_t Lsv_SimulateNode(Abc_Ntk_t* pNtk, int nodeId,
                                 std::unordered_map<int, uint64_t>& simValues) {
  //hit: cut leaf node or already-computed internal node
  auto it = simValues.find(nodeId);
  if (it != simValues.end()) {
    return it->second;
  }

  Abc_Obj_t* pObj = Abc_NtkObj(pNtk, nodeId);

  // Constant-1 node: all bits are 1
  if (pObj == Abc_AigConst1(pNtk)) {
    uint64_t val = ~(uint64_t)0;  // 0xFFFFFFFFFFFFFFFF
    simValues[nodeId] = val;
    return val;
  }

  // Simulate both fanins, then apply complement and AND.
  Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pObj);
  Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pObj);

  uint64_t val0 = Lsv_SimulateNode(pNtk, Abc_ObjId(pFanin0), simValues);
  uint64_t val1 = Lsv_SimulateNode(pNtk, Abc_ObjId(pFanin1), simValues);

  // inverters on AIG edges
  if (Abc_ObjFaninC0(pObj)) val0 = ~val0;
  if (Abc_ObjFaninC1(pObj)) val1 = ~val1;

  uint64_t result = val0 & val1;
  simValues[nodeId] = result;
  return result;
}

// Computes the truth table ， Returns lower 2^n bits holding the truth table
static uint64_t Lsv_ComputeCutTruthTable(Abc_Ntk_t* pNtk, int targetNodeId,
                                         const std::vector<int>& cut) {
  int n = static_cast<int>(cut.size());
  std::unordered_map<int, uint64_t> simValues;

  // Assign standard input patterns to cut leaf nodes.
  for (int j = 0; j < n; ++j) {
    simValues[cut[j]] = kInputPatterns[n - 1 - j];
  }

  // Simulate target node to cut leaves.
  uint64_t rawTT = Lsv_SimulateNode(pNtk, targetNodeId, simValues);

  // Mask to 2^n significant bits.
  uint64_t mask = (n < 6) ? ((1ULL << (1 << n)) - 1) : ~(uint64_t)0;
  return rawTT & mask;
}

// lsv_cut_tt <k>

static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv) {
  // --- Argument validation ---
  if (argc != 2) {
    Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
    Abc_Print(-2, "\t        enumerates k-feasible cuts with truth tables\n");
    Abc_Print(-2, "\t<k>   : cut size limit (2 <= k <= 6)\n");
    return 1;
  }

  int k = atoi(argv[1]);
  if (k < 2 || k > 6) {
    Abc_Print(-1, "Error: k must be between 2 and 6.\n");
    return 1;
  }

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1,
              "Error: network is not a strashed AIG. Run \"strash\" first.\n");
    return 1;
  }

  // --- Phase 2: enumerate all k-feasible cuts ---
  std::map<int, std::vector<std::vector<int>>> nodeCuts =
      Lsv_NtkEnumerateCuts(pNtk, k);

  // --- Phase 3: compute truth tables and print for internal AND nodes ---
  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int nid = Abc_ObjId(pObj);
    const std::vector<std::vector<int>>& cuts = nodeCuts[nid];
    for (const auto& cut : cuts) {
      int n = static_cast<int>(cut.size());

      // Compute truth table
      uint64_t tt = Lsv_ComputeCutTruthTable(pNtk, nid, cut);

      // Determine hex width:(2^n / 4) hex digits
      int numBits = 1 << n;
      int hexWidth = (numBits + 3) / 4;  // ceil division by 4

      // Print: <node_id>: <cut_id_0> <cut_id_1> ... : <hex_truth_table>
      printf("%d:", nid);
      for (int j = 0; j < n; ++j) {
        printf(" %d", cut[j]);
      }
      printf(": %0*llX\n", hexWidth, (unsigned long long)tt);
    }
  }

  return 0;
}

// ============================================================
//  Phase 4: Recursive BDD Construction for Cut BDD Sizes
// ============================================================

// Recursively builds the BDD for 'nodeId' from the target node down to the cut leaves.

static DdNode* Lsv_BuildBddNode(Abc_Ntk_t* pNtk, int nodeId, DdManager* dd,
                                 std::unordered_map<int, DdNode*>& bddCache) {
  //hit: cut leaf node or already-computed internal node
  auto it = bddCache.find(nodeId);
  if (it != bddCache.end()) {
    return it->second;
  }

  Abc_Obj_t* pObj = Abc_NtkObj(pNtk, nodeId);

  // Constant-1 node
  if (pObj == Abc_AigConst1(pNtk)) {
    DdNode* one = Cudd_ReadOne(dd);
    Cudd_Ref(one);
    bddCache[nodeId] = one;
    return one;
  }


  Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pObj);
  Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pObj);

  DdNode* bdd0 = Lsv_BuildBddNode(pNtk, Abc_ObjId(pFanin0), dd, bddCache);
  DdNode* bdd1 = Lsv_BuildBddNode(pNtk, Abc_ObjId(pFanin1), dd, bddCache);

  // Handle complemented edges.
  if (Abc_ObjFaninC0(pObj)) bdd0 = Cudd_Not(bdd0);
  if (Abc_ObjFaninC1(pObj)) bdd1 = Cudd_Not(bdd1);

  // Compute AND and ref the result
  DdNode* result = Cudd_bddAnd(dd, bdd0, bdd1);
  Cudd_Ref(result);
  bddCache[nodeId] = result;
  return result;
}


// lsv_cut_bddsize <k>
static int Lsv_CommandCutBDDSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  // --- Argument validation ---
  if (argc != 2) {
    Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
    Abc_Print(-2, "\t        enumerates k-feasible cuts with BDD sizes\n");
    Abc_Print(-2, "\t<k>   : cut size limit (2 <= k <= 6)\n");
    return 1;
  }

  int k = atoi(argv[1]);
  if (k < 2 || k > 6) {
    Abc_Print(-1, "Error: k must be between 2 and 6.\n");
    return 1;
  }

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1,
              "Error: network is not a strashed AIG. Run \"strash\" first.\n");
    return 1;
  }

  // --- Phase 2: enumerate all k-feasible cuts ---
  std::map<int, std::vector<std::vector<int>>> nodeCuts =
      Lsv_NtkEnumerateCuts(pNtk, k);

  // --- Phase 4: build BDDs and print sizes for internal AND nodes ---

  // Initialize a shared CUDD manager with k BDD variables.
  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  if (!dd) {
    Abc_Print(-1, "Error: failed to initialize CUDD manager.\n");
    return 1;
  }

  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int nid = Abc_ObjId(pObj);
    const std::vector<std::vector<int>>& cuts = nodeCuts[nid];

    for (const auto& cut : cuts) {
      int n = static_cast<int>(cut.size());

      std::unordered_map<int, DdNode*> bddCache;

      // Initialize cut leaf nodes as BDD variables.
      for (int j = 0; j < n; ++j) {
        DdNode* var = Cudd_bddIthVar(dd, j);
        Cudd_Ref(var);
        bddCache[cut[j]] = var;
      }

      // Recursively build the BDD for the target node
      DdNode* bddRoot = Lsv_BuildBddNode(pNtk, nid, dd, bddCache);

      // Compute BDD size 
      int bddSize = Cudd_DagSize(bddRoot);

      // Print: <node_id>: <cut_id_0> <cut_id_1> ... : <bdd_size>
      printf("%d:", nid);
      for (int j = 0; j < n; ++j) {
        printf(" %d", cut[j]);
      }
      printf(": %d\n", bddSize);

      // Cleanup
      for (auto& entry : bddCache) {
        Cudd_RecursiveDeref(dd, entry.second);
      }
    }
  }
  Cudd_Quit(dd);

  return 0;
}