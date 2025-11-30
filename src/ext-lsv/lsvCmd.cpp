extern "C" {
#include "base/abc/abc.h"
#include "bdd/cudd/cudd.h"
#include "aig/aig/aig.h"
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "misc/vec/vec.h"
#include "sat/cnf/cnf.h"
#include <set>
#include <map>
#include <vector>
#include <algorithm>
#include <string>
#include <cstring>
#include <numeric>

// ================================================================
//  Function Declarations
// ================================================================
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);
static void Lsv_EnumerateCuts(Abc_Obj_t* pNode, int k, std::map<int, std::set<std::set<int>>>& memo, std::set<std::set<int>>& cuts);
static int Lsv_FindPiIndexByName(Abc_Ntk_t* pNtk, const char* name);
static bool Lsv_PrintPattern(DdManager* dd, const std::vector<int>& origVarIndex, int origPiIndex, DdNode* bFunc);
static bool Lsv_IsSubsequence(const std::vector<int>& subseq, const std::vector<int>& seq);
static bool Lsv_GuessBddReverse(Abc_Ntk_t* pNtk, DdManager* dd, const std::vector<int>& objIdToCiIdx);

// ================================================================
//  Initialization and Registration
// ================================================================
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMocut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// ================================================================
//  Command: lsv_print_nodes
// ================================================================
void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n",
             j, Abc_ObjId(pFanin), Abc_ObjName(pFanin));
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

// ================================================================
//  Helper: Recursive k-feasible Cut Enumeration (with cache)
// ================================================================
void Lsv_EnumerateCuts(Abc_Obj_t* pNode, int k,
                       std::map<int, std::set<std::set<int>>>& memo,
                       std::set<std::set<int>>& cuts) {
  int id = Abc_ObjId(pNode);
  if (memo.count(id)) {
    cuts = memo[id];
    return;
  }

  if (Abc_ObjIsPi(pNode)) {
    cuts.insert({id});
    memo[id] = cuts;
    return;
  }

  Abc_Obj_t* pF0 = Abc_ObjFanin0(pNode);
  Abc_Obj_t* pF1 = Abc_ObjFanin1(pNode);
  std::set<std::set<int>> cuts0, cuts1;
  Lsv_EnumerateCuts(pF0, k, memo, cuts0);
  Lsv_EnumerateCuts(pF1, k, memo, cuts1);

  for (auto& c0 : cuts0)
    for (auto& c1 : cuts1) {
      std::set<int> merged = c0;
      merged.insert(c1.begin(), c1.end());
      if ((int)merged.size() <= k) {
        // irredundant check
        bool redundant = false;
        for (auto& existing : cuts) {
          if (std::includes(existing.begin(), existing.end(),
                            merged.begin(), merged.end())) {
            redundant = true;
            break;
          }
        }
        if (!redundant) cuts.insert(merged);
      }
    }

  // Add trivial cut itself
  cuts.insert({id});
  memo[id] = cuts;
}

// ================================================================
//  Command: lsv_printmocut
// ================================================================
int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network must be an AIG. Run 'strash' first.\n");
    return 1;
  }

  if (argc < 3) {
    Abc_Print(-1, "usage: lsv_printmocut <k> <l>\n");
    return 1;
  }

  int k = atoi(argv[1]);
  int l = atoi(argv[2]);
  if (k < 3 || k > 6) {
    Abc_Print(-1, "k must be between 3 and 6.\n");
    return 1;
  }
  if (l < 1 || l > 4) {
    Abc_Print(-1, "l must be between 1 and 4.\n");
    return 1;
  }

  std::map<std::set<int>, std::set<int>> cut_to_outputs;
  std::map<int, std::set<std::set<int>>> memo;

  Abc_Obj_t* pNode;
  int i;
  Abc_NtkForEachNode(pNtk, pNode, i) {
    if (!Abc_AigNodeIsAnd(pNode)) continue;

    std::set<std::set<int>> cuts;
    Lsv_EnumerateCuts(pNode, k, memo, cuts);

    for (auto& cut : cuts)
      cut_to_outputs[cut].insert(Abc_ObjId(pNode));
  }

  // also consider PIs as outputs (for completeness)
  Abc_NtkForEachPi(pNtk, pNode, i) {
    std::set<int> trivial_cut = {static_cast<int>(Abc_ObjId(pNode))};
    cut_to_outputs[trivial_cut].insert(static_cast<int>(Abc_ObjId(pNode)));
  }

  // Print all multi-output cuts
  for (auto& kv : cut_to_outputs) {
    const std::set<int>& inputs = kv.first;
    const std::set<int>& outputs = kv.second;
    if ((int)outputs.size() < l) continue;

    bool first = true;
    for (int in_id : inputs) {
      if (!first) printf(" ");
      printf("%d", in_id);
      first = false;
    }
    printf(" : ");
    first = true;
    for (int out_id : outputs) {
      if (!first) printf(" ");
      printf("%d", out_id);
      first = false;
    }
    printf("\n");
  }

  return 0;
}

static int Lsv_FindPiIndexByName(Abc_Ntk_t* pNtk, const char* name) {
  if (!name) return -1;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPi(pNtk, pObj, i) {
    if (Abc_ObjName(pObj) && strcmp(Abc_ObjName(pObj), name) == 0) return i;
  }
  return -1;
}

static bool Lsv_PrintPattern(DdManager* dd, const std::vector<int>& origVarIndex, int origPiIndex, DdNode* bFunc) {
  int nVars = Cudd_ReadSize(dd);
  char* cube = ABC_ALLOC(char, nVars);
  for (int k = 0; k < nVars; ++k) cube[k] = 2;
  int ok = Cudd_bddPickOneCube(dd, bFunc, cube);
  if (!ok) {
    ABC_FREE(cube);
    return false;
  }

  int nPiOrig = (int)origVarIndex.size();
  for (int idx = 0; idx < nPiOrig; ++idx) {
    if (idx == origPiIndex) {
      printf("-");
      continue;
    }
    int varIdx = (idx >= 0 && idx < (int)origVarIndex.size()) ? origVarIndex[idx] : -1;
    int bit = (varIdx >= 0 && varIdx < nVars) ? cube[varIdx] : 2;
    if (bit == 0 || bit == 1)
      printf("%d", bit);
    else printf("0");
  }
  printf("\n");
  ABC_FREE(cube);
  return true;
}

// ================================================================
//  Command: lsv_unate_bdd
// ================================================================
int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (argc < 3) {
    Abc_Print(-1, "usage: lsv_unate_bdd <k> <i>\n");
    Abc_Print(-1, "        k: primary output index (starting from 0)\n");
    Abc_Print(-1, "        i: primary input index (starting from 0)\n");
    return 1;
  }

  int k = atoi(argv[1]);
  int i = atoi(argv[2]);

  if (k < 0 || k >= Abc_NtkCoNum(pNtk)) {
    Abc_Print(-1, "Invalid output index %d. Valid range: 0 to %d\n", k, Abc_NtkCoNum(pNtk) - 1);
    return 1;
  }

  int nPisOrig = Abc_NtkPiNum(pNtk);
  if (nPisOrig == 0) {
    Abc_Print(-1, "Network has no primary inputs.\n");
    return 1;
  }
  if (i < 0 || i >= nPisOrig) {
    Abc_Print(-1, "Invalid input index %d. Valid range: 0 to %d\n", i, nPisOrig - 1);
    return 1;
  }

  Abc_Ntk_t* pStrash = Abc_NtkStrash(pNtk, 0, 0, 0);
  if (!pStrash) {
    Abc_Print(-1, "Failed to strash the network.\n");
    return 1;
  }

  DdManager* dd = (DdManager*)Abc_NtkBuildGlobalBdds(pStrash, 10000000, 1, 1, 0, 0);
  if (!dd) {
    Abc_NtkDelete(pStrash);
    Abc_Print(-1, "Failed to build global BDDs.\n");
    return 1;
  }

  if (Abc_NtkPiNum(pStrash) != nPisOrig) {
    Abc_Print(-1, "Internal error: PI count mismatch after strashing.\n");
    Abc_NtkFreeGlobalBdds(pStrash, 1);
    Abc_NtkDelete(pStrash);
    return 1;
  }

  std::vector<int> origVarIndex(nPisOrig);
  std::iota(origVarIndex.begin(), origVarIndex.end(), 0);

  Abc_Obj_t* pCo = Abc_NtkCo(pStrash, k);
  DdNode* bFunc = (DdNode*)Abc_ObjGlobalBdd(pCo);
  if (!bFunc) {
    Abc_Print(-1, "Output %d has no BDD representation.\n", k);
    Abc_NtkFreeGlobalBdds(pStrash, 1);
    Abc_NtkDelete(pStrash);
    return 1;
  }
  Cudd_Ref(bFunc);

  int nVars = Cudd_ReadSize(dd);
  if (i >= nVars) {
    Abc_Print(-1, "PI index %d exceeds BDD variable count %d.\n", i, nVars);
    Cudd_RecursiveDeref(dd, bFunc);
    Abc_NtkFreeGlobalBdds(pStrash, 1);
    Abc_NtkDelete(pStrash);
    return 1;
  }

  DdNode* bVar = Cudd_bddIthVar(dd, i);
  if (!bVar) {
    Abc_Print(-1, "Unable to access BDD variable %d.\n", i);
    Cudd_RecursiveDeref(dd, bFunc);
    Abc_NtkFreeGlobalBdds(pStrash, 1);
    Abc_NtkDelete(pStrash);
    return 1;
  }
  Cudd_Ref(bVar);

  DdNode* bZero = Cudd_Not(Cudd_ReadOne(dd));
  Cudd_Ref(bZero);
  DdNode* bOne = Cudd_ReadOne(dd);
  Cudd_Ref(bOne);

  DdNode* bCof0 = Cudd_bddCompose(dd, bFunc, bZero, i);
  if (!bCof0) {
    Abc_Print(-1, "Failed to compute cofactor for xi=0.\n");
    Cudd_RecursiveDeref(dd, bZero);
    Cudd_RecursiveDeref(dd, bOne);
    Cudd_RecursiveDeref(dd, bVar);
    Cudd_RecursiveDeref(dd, bFunc);
    Abc_NtkFreeGlobalBdds(pStrash, 1);
    Abc_NtkDelete(pStrash);
    return 1;
  }
  Cudd_Ref(bCof0);

  DdNode* bCof1 = Cudd_bddCompose(dd, bFunc, bOne, i);
  if (!bCof1) {
    Abc_Print(-1, "Failed to compute cofactor for xi=1.\n");
    Cudd_RecursiveDeref(dd, bCof0);
    Cudd_RecursiveDeref(dd, bZero);
    Cudd_RecursiveDeref(dd, bOne);
    Cudd_RecursiveDeref(dd, bVar);
    Cudd_RecursiveDeref(dd, bFunc);
    Abc_NtkFreeGlobalBdds(pStrash, 1);
    Abc_NtkDelete(pStrash);
    return 1;
  }
  Cudd_Ref(bCof1);
  Cudd_RecursiveDeref(dd, bZero);
  Cudd_RecursiveDeref(dd, bOne);

  bool isPositiveUnate = Cudd_bddLeq(dd, bCof0, bCof1);
  bool isNegativeUnate = Cudd_bddLeq(dd, bCof1, bCof0);
  bool isIndependent = isPositiveUnate && isNegativeUnate;

  if (isIndependent) {
    printf("independent\n");
  } else if (isPositiveUnate) {
    printf("positive unate\n");
  } else if (isNegativeUnate) {
    printf("negative unate\n");
  } else {
    printf("binate\n");
    DdNode* bPatternRaise = Cudd_bddAnd(dd, Cudd_Not(bCof0), bCof1);
    if (!bPatternRaise) {
      Abc_Print(-1, "Failed to derive witness for xi leading to 1.\n");
      Cudd_RecursiveDeref(dd, bCof1);
      Cudd_RecursiveDeref(dd, bCof0);
      Cudd_RecursiveDeref(dd, bVar);
      Cudd_RecursiveDeref(dd, bFunc);
      Abc_NtkFreeGlobalBdds(pStrash, 1);
      Abc_NtkDelete(pStrash);
      return 1;
    }
    Cudd_Ref(bPatternRaise);
    if (!Lsv_PrintPattern(dd, origVarIndex, i, bPatternRaise)) {
      Abc_Print(-1, "Unable to print witness pattern for xi.\n");
      Cudd_RecursiveDeref(dd, bPatternRaise);
      Cudd_RecursiveDeref(dd, bCof1);
      Cudd_RecursiveDeref(dd, bCof0);
      Cudd_RecursiveDeref(dd, bVar);
      Cudd_RecursiveDeref(dd, bFunc);
      Abc_NtkFreeGlobalBdds(pStrash, 1);
      Abc_NtkDelete(pStrash);
      return 1;
    }
    Cudd_RecursiveDeref(dd, bPatternRaise);

    DdNode* bPatternFall = Cudd_bddAnd(dd, bCof0, Cudd_Not(bCof1));
    if (!bPatternFall) {
      Abc_Print(-1, "Failed to derive witness for ¬xi leading to 0.\n");
      Cudd_RecursiveDeref(dd, bCof1);
      Cudd_RecursiveDeref(dd, bCof0);
      Cudd_RecursiveDeref(dd, bVar);
      Cudd_RecursiveDeref(dd, bFunc);
      Abc_NtkFreeGlobalBdds(pStrash, 1);
      Abc_NtkDelete(pStrash);
      return 1;
    }
    Cudd_Ref(bPatternFall);
    if (!Lsv_PrintPattern(dd, origVarIndex, i, bPatternFall)) {
      Abc_Print(-1, "Unable to print witness pattern for ¬xi.\n");
      Cudd_RecursiveDeref(dd, bPatternFall);
      Cudd_RecursiveDeref(dd, bCof1);
      Cudd_RecursiveDeref(dd, bCof0);
      Cudd_RecursiveDeref(dd, bVar);
      Cudd_RecursiveDeref(dd, bFunc);
      Abc_NtkFreeGlobalBdds(pStrash, 1);
      Abc_NtkDelete(pStrash);
      return 1;
    }
    Cudd_RecursiveDeref(dd, bPatternFall);
  }

  Cudd_RecursiveDeref(dd, bCof1);
  Cudd_RecursiveDeref(dd, bCof0);
  Cudd_RecursiveDeref(dd, bVar);
  Cudd_RecursiveDeref(dd, bFunc);

  Abc_NtkFreeGlobalBdds(pStrash, 1);
  Abc_NtkDelete(pStrash);
  return 0;
}

// ================================================================
//  Command: lsv_unate_sat
// ================================================================
int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network must be an AIG. Run 'strash' first.\n");
    return 1;
  }

  if (argc < 3) {
    Abc_Print(-1, "usage: lsv_unate_sat <k> <i>\n");
    Abc_Print(-1, "        k: primary output index (starting from 0)\n");
    Abc_Print(-1, "        i: primary input index (starting from 0)\n");
    return 1;
  }

  int k = atoi(argv[1]);
  int i = atoi(argv[2]);

  if (k < 0 || k >= Abc_NtkCoNum(pNtk)) {
    Abc_Print(-1, "Invalid output index %d. Valid range: 0 to %d\n", k, Abc_NtkCoNum(pNtk) - 1);
    return 1;
  }

  if (i < 0 || i >= Abc_NtkCiNum(pNtk)) {
    Abc_Print(-1, "Invalid input index %d. Valid range: 0 to %d\n", i, Abc_NtkCiNum(pNtk) - 1);
    return 1;
  }

  // Step 1: Extract cone of output yk
  Abc_Obj_t* pOutput = Abc_NtkCo(pNtk, k);
  int fOutputCompl = Abc_ObjFaninC0(pOutput);
  Abc_Obj_t* pDriver = Abc_ObjFanin0(pOutput);
  Abc_Ntk_t* pNtkCone = Abc_NtkCreateCone(pNtk, pDriver, "cone", 1);
  if (!pNtkCone) {
    Abc_Print(-1, "Failed to create cone for output %d.\n", k);
    return 1;
  }

  // Get the input object in the original network
  Abc_Obj_t* pInputOrig = Abc_NtkCi(pNtk, i);
  
  // Find the corresponding input in the cone and get its index
  // Since fUseAllCis=1, all inputs are included, but order may differ
  int iCone = -1;
  Abc_Obj_t* pObj;
  int j;  // Loop variable for iterating inputs
  Abc_NtkForEachCi(pNtkCone, pObj, j) {
    if (pObj == (Abc_Obj_t*)pInputOrig->pCopy) {
      iCone = j;
      break;
    }
  }
  
  if (iCone < 0) {
    Abc_NtkDelete(pNtkCone);
    Abc_Print(-1, "Input %d not found in cone.\n", i);
    return 1;
  }
  
  // Step 2: Convert to AIG
  Aig_Man_t* pAig = Abc_NtkToDar(pNtkCone, 0, 0);
  Abc_NtkDelete(pNtkCone);
  if (!pAig) {
    Abc_Print(-1, "Failed to convert cone to AIG.\n");
    return 1;
  }
  
  // Find the index of the input in AIG
  // Abc_NtkToDar preserves the order of inputs from the cone
  // So iCone should map to the same index in AIG
  int iAig = iCone;
  
  // Verify the index is valid
  if (iAig >= Aig_ManCiNum(pAig)) {
    Aig_ManStop(pAig);
    Abc_Print(-1, "Input index %d exceeds AIG input count %d.\n", iAig, Aig_ManCiNum(pAig));
    return 1;
  }
  
  // Update i to use the AIG index
  i = iAig;

  // Step 3: Initialize SAT solver
  sat_solver* pSat = sat_solver_new();
  if (!pSat) {
    Aig_ManStop(pAig);
    Abc_Print(-1, "Failed to create SAT solver.\n");
    return 1;
  }

  // Step 4: Derive CNF for CA
  Cnf_Dat_t* pCnfA = Cnf_Derive(pAig, Aig_ManCoNum(pAig));
  if (!pCnfA) {
    sat_solver_delete(pSat);
    Aig_ManStop(pAig);
    Abc_Print(-1, "Failed to derive CNF.\n");
    return 1;
  }

  // Step 5: Add CNF A to SAT solver
  pSat = (sat_solver*)Cnf_DataWriteIntoSolverInt(pSat, pCnfA, 1, 0);
  if (!pSat) {
    Cnf_DataFree(pCnfA);
    Aig_ManStop(pAig);
    Abc_Print(-1, "Failed to add CNF A to SAT solver.\n");
    return 1;
  }

  // Step 6: Create CNF B with different variables
  Cnf_Dat_t* pCnfB = Cnf_Derive(pAig, Aig_ManCoNum(pAig));
  if (!pCnfB) {
    Cnf_DataFree(pCnfA);
    sat_solver_delete(pSat);
    Aig_ManStop(pAig);
    Abc_Print(-1, "Failed to derive second CNF.\n");
    return 1;
  }
  Cnf_DataLift(pCnfB, pCnfA->nVars);
  
  // Add CNF B to SAT solver
  pSat = (sat_solver*)Cnf_DataWriteIntoSolverInt(pSat, pCnfB, 1, 0);
  if (!pSat) {
    Cnf_DataFree(pCnfA);
    Cnf_DataFree(pCnfB);
    Aig_ManStop(pAig);
    Abc_Print(-1, "Failed to add CNF B to SAT solver.\n");
    return 1;
  }

  // Step 7: For each input xt (except xi), set vA(t) = vB(t)
  Aig_Obj_t* pObjCi;
  int Lits[2];
  int nCi = Aig_ManCiNum(pAig);
  // j is already declared above, reuse it here
  
  Aig_ManForEachCi(pAig, pObjCi, j) {
    if (j == i) continue;  // Skip xi
    
    int varA = pCnfA->pVarNums[Aig_ObjId(pObjCi)];
    int varB = pCnfB->pVarNums[Aig_ObjId(pObjCi)];
    
    // Add clauses: (varA -> varB) and (varB -> varA)
    // Which is: (-varA | varB) and (varA | -varB)
    Lits[0] = toLitCond(varA, 1);  // -varA
    Lits[1] = toLitCond(varB, 0);  // varB
    if (!sat_solver_addclause(pSat, Lits, Lits + 2)) {
      Cnf_DataFree(pCnfA);
      Cnf_DataFree(pCnfB);
      sat_solver_delete(pSat);
      Aig_ManStop(pAig);
      Abc_Print(-1, "Failed to add equality clauses.\n");
      return 1;
    }
    
    Lits[0] = toLitCond(varA, 0);  // varA
    Lits[1] = toLitCond(varB, 1);  // -varB
    if (!sat_solver_addclause(pSat, Lits, Lits + 2)) {
      Cnf_DataFree(pCnfA);
      Cnf_DataFree(pCnfB);
      sat_solver_delete(pSat);
      Aig_ManStop(pAig);
      Abc_Print(-1, "Failed to add equality clauses.\n");
      return 1;
    }
  }

  // Get output variables
  // Note: Cnf_Derive with nOutputs > 0 creates variables for output nodes
  // The output variable represents the output value directly (inversion is handled in CNF)
  Aig_Obj_t* pObjCo = Aig_ManCo(pAig, 0);
  Aig_Obj_t* pOutFanin = Aig_ObjFanin0(pObjCo);
  int litOutA = toLitCond(pCnfA->pVarNums[Aig_ObjId(pOutFanin)], Aig_ObjFaninC0(pObjCo));
  int litOutB = toLitCond(pCnfB->pVarNums[Aig_ObjId(pOutFanin)], Aig_ObjFaninC0(pObjCo));
  if (fOutputCompl) {
    litOutA ^= 1;
    litOutB ^= 1;
  }
  
  // Get input xi variables
  Aig_Obj_t* pObjXi = Aig_ManCi(pAig, i);
  int varXiA = pCnfA->pVarNums[Aig_ObjId(pObjXi)];
  int varXiB = pCnfB->pVarNums[Aig_ObjId(pObjXi)];

  // Step 8: Check unateness using SAT
  int assumptions[4];
  int status;
  
  // Check positive unate: (xiA=0, xiB=1) and (outA=1, outB=0) should be UNSAT
  // Positive unate means: f|xi=0 <= f|xi=1, i.e., if xi increases, output cannot decrease
  // So we check: exists pattern where (xiA=0, xiB=1) and (outA=1, outB=0)
  assumptions[0] = toLitCond(varXiA, 1); // xiA = 0
  assumptions[1] = toLitCond(varXiB, 0); // xiB = 1
  assumptions[2] = litOutA;        // outA = 1
  assumptions[3] = litOutB ^ 1;    // outB = 0
  status = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
  int isPositiveUnate = (status == l_False);

  // Check negative unate: (xiA=0, xiB=1) and (outA=0, outB=1) should be UNSAT
  // Negative unate means: f|xi=1 <= f|xi=0, i.e., increasing xi cannot increase output
  // So we check: exists pattern where (xiA=0, xiB=1) and (outA=0, outB=1)
  assumptions[0] = toLitCond(varXiA, 1); // xiA = 0
  assumptions[1] = toLitCond(varXiB, 0); // xiB = 1
  assumptions[2] = litOutA ^ 1;    // outA = 0
  assumptions[3] = litOutB;        // outB = 1
  status = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
  int isNegativeUnate = (status == l_False);

  // Independent iff both positive/negative unateness hold simultaneously
  int isIndependent = isPositiveUnate && isNegativeUnate;

  if (isIndependent) {
    printf("independent\n");
  } else if (isPositiveUnate) {
    printf("positive unate\n");
  } else if (isNegativeUnate) {
    printf("negative unate\n");
  } else {
    // Binate: find two patterns
    printf("binate\n");
    
    // Pattern 1: f|Pattern1 = xi
    // This means: (xiA=0, xiB=1) -> (outA=0, outB=1)
    assumptions[0] = toLitCond(varXiA, 1); // xiA = 0
    assumptions[1] = toLitCond(varXiB, 0); // xiB = 1
    assumptions[2] = litOutA ^ 1;  // outA = 0
    assumptions[3] = litOutB;      // outB = 1
    
    status = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
    if (status == l_True) {
      // Get satisfying assignment
      for (int j = 0; j < nCi; j++) {
        if (j == i) {
          printf("-");
        } else {
          Aig_Obj_t* pObj = Aig_ManCi(pAig, j);
          int var = pCnfA->pVarNums[Aig_ObjId(pObj)];
          int value = sat_solver_var_value(pSat, var);
          printf("%d", value);
        }
      }
      printf("\n");
    }
    
    // Pattern 2: f|Pattern2 = ¬xi
    // This means: (xiA=0, xiB=1) -> (outA=1, outB=0)
    assumptions[0] = toLitCond(varXiA, 1); // xiA = 0
    assumptions[1] = toLitCond(varXiB, 0); // xiB = 1
    assumptions[2] = litOutA;      // outA = 1
    assumptions[3] = litOutB ^ 1;  // outB = 0
    
    status = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
    if (status == l_True) {
      // Get satisfying assignment
      for (int j = 0; j < nCi; j++) {
        if (j == i) {
          printf("-");
        } else {
          Aig_Obj_t* pObj = Aig_ManCi(pAig, j);
          int var = pCnfA->pVarNums[Aig_ObjId(pObj)];
          int value = sat_solver_var_value(pSat, var);
          printf("%d", value);
        }
      }
      printf("\n");
    }
  }

  // Cleanup
  Cnf_DataFree(pCnfA);
  Cnf_DataFree(pCnfB);
  sat_solver_delete(pSat);
  Aig_ManStop(pAig);

  return 0;
}

