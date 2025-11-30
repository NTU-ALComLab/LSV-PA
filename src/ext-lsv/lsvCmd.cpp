#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <string>
#include <iostream>

extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintKLCuts(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocuts", Lsv_CommandPrintKLCuts, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);

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
        goto usage_lsv_print_nodes;
      default:
        goto usage_lsv_print_nodes;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage_lsv_print_nodes:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

// Helper function to check if a set is irredundant (no subset is also a cut)
bool Lsv_IsIrredundant(const std::set<int>& cut, Abc_Obj_t* pNode, Abc_Ntk_t* pNtk) {
  // Try removing each element to see if it's still a cut
  for (int elem : cut) {
    std::set<int> subset = cut;
    subset.erase(elem);
    
    // Check if subset is still a cut (using BFS/DFS)
    std::set<int> visited;
    std::vector<int> queue;
    queue.push_back(pNode->Id);
    visited.insert(pNode->Id);
    
    bool isStillCut = true;
    while (!queue.empty() && isStillCut) {
      int current = queue.back();
      queue.pop_back();
      
      if (subset.count(current) > 0) {
        continue; // This is a cut node
      }
      
      Abc_Obj_t* pCurr = Abc_NtkObj(pNtk, current);
      if (Abc_ObjIsPi(pCurr)) {
        if (subset.count(current) == 0) {
          isStillCut = false; // Reached PI not in subset
        }
      } else if (Abc_ObjIsNode(pCurr)) {
        Abc_Obj_t* pFanin;
        int j;
        Abc_ObjForEachFanin(pCurr, pFanin, j) {
          int faninId = Abc_ObjId(pFanin);
          if (visited.find(faninId) == visited.end()) {
            visited.insert(faninId);
            queue.push_back(faninId);
          }
        }
      }
    }
    
    if (isStillCut) {
      return false; // Found a subset that is also a cut
    }
  }
  return true;
}

// Compute k-feasible cuts for a single node
void Lsv_EnumKFeasibleCuts(Abc_Obj_t* pNode, int K, Abc_Ntk_t* pNtk, 
                          std::vector<std::set<int>>& cuts) {
  cuts.clear();
  
  // Trivial cut: the node itself
  if (Abc_ObjIsPi(pNode)) {
    cuts.push_back({pNode->Id});
    return;
  }
  
  // For internal nodes, use BFS to enumerate cuts
  std::set<std::set<int>> allCuts;
  
  // Start with trivial cut
  allCuts.insert({pNode->Id});
  
  // BFS to find all cuts
  std::vector<std::set<int>> frontier;
  frontier.push_back({pNode->Id});
  
  while (!frontier.empty()) {
    std::set<int> current = frontier.back();
    frontier.pop_back();
    
    // Try expanding each node in current cut
    for (int nodeId : current) {
      Abc_Obj_t* pCurr = Abc_NtkObj(pNtk, nodeId);
      
      if (!Abc_ObjIsNode(pCurr)) continue; // Skip PIs
      
      // Create new cut by replacing this node with its fanins
      std::set<int> newCut = current;
      newCut.erase(nodeId);
      
      Abc_Obj_t* pFanin;
      int j;
      Abc_ObjForEachFanin(pCurr, pFanin, j) {
        newCut.insert(Abc_ObjId(pFanin));
      }
      
      // Check if this is a valid k-feasible cut
      if (newCut.size() <= K && allCuts.find(newCut) == allCuts.end()) {
        allCuts.insert(newCut);
        frontier.push_back(newCut);
      }
    }
  }
  
  // Filter to keep only irredundant cuts
  for (const auto& cut : allCuts) {
    if (Lsv_IsIrredundant(cut, pNode, pNtk)) {
      cuts.push_back(cut);
    }
  }
}

void Lsv_PrintKLCuts(Abc_Ntk_t* pNtk, int K, int L) {
  // Map from cut to set of output nodes
  std::map<std::set<int>, std::set<int>> cutToOutputs;
  
  // Compute cuts for each node
  Abc_Obj_t* pObj;
  int i;
  
  // Process all nodes (internal AND nodes and PIs)
  Abc_NtkForEachNode(pNtk, pObj, i) {
    std::vector<std::set<int>> cuts;
    Lsv_EnumKFeasibleCuts(pObj, K, pNtk, cuts);
    
    // Add this node as output for each of its cuts
    for (const auto& cut : cuts) {
      cutToOutputs[cut].insert(Abc_ObjId(pObj));
    }
  }
  
  // Also process primary inputs
  Abc_NtkForEachPi(pNtk, pObj, i) {
    std::vector<std::set<int>> cuts;
    Lsv_EnumKFeasibleCuts(pObj, K, pNtk, cuts);
    
    // Add this node as output for each of its cuts
    for (const auto& cut : cuts) {
      cutToOutputs[cut].insert(Abc_ObjId(pObj));
    }
  }
  
  // Print the cuts that have at least L outputs
  for (const auto& pair : cutToOutputs) {
    if (pair.second.size() >= L) {
      // Print inputs (sorted)
      bool first = true;
      for (int input : pair.first) {
        if (!first) printf(" ");
        printf("%d", input);
        first = false;
      }
      
      printf(" : ");
      
      // Print outputs (sorted)
      first = true;
      for (int output : pair.second) {
        if (!first) printf(" ");
        printf("%d", output);
        first = false;
      }
      
      printf("\n");
    }
  }
}

int Lsv_CommandPrintKLCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int K = 3, L = 1;

  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "k:l:h")) != EOF) {
    switch (c) {
      case 'k':
        K = atoi(globalUtilOptarg);
        if (K < 3 || K > 6) {
          Abc_Print(-1, "K should be between 3 and 6.\n");
          goto usage_lsv_printmocuts;
        }
        break;
      case 'l':
        L = atoi(globalUtilOptarg);
        if (L < 1 || L > 4) {
          Abc_Print(-1, "L should be between 1 and 4.\n");
          goto usage_lsv_printmocuts;
        }
        break;
      case 'h':
        goto usage_lsv_printmocuts;
      default:
        goto usage_lsv_printmocuts;
    }
  }
  
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  
  // Check if network is strashed (AIG)
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not strashed. Please run 'strash' first.\n");
    return 1;
  }
  
  Lsv_PrintKLCuts(pNtk, K, L);
  return 0;

usage_lsv_printmocuts:
  Abc_Print(-2, "usage: lsv_printmocuts [-k K] [-l L] [-h]\n");
  Abc_Print(-2, "options: \n");
  Abc_Print(-2, "\t-k K\tEnumeration for at most K inputs (Default 3, 3 <= K <= 6)\n");
  Abc_Print(-2, "\t-l L\tEnumeration for at least L outputs (Default 1, 1 <= L <= 4)\n");
  Abc_Print(-2, "\t-h  \tPrint the command usage\n");
  return 1;
}


/* Exercise 1 : Unateness Checking with BDD */

// Find a cube that makes the cofactor equal to xi or !xi
bool Lsv_FindBinateCube(DdManager* dd, DdNode* func, int varIndex, 
                       int nPis, int piIndex,
                       std::string& pattern1, std::string& pattern2) {
  DdNode* var = Cudd_bddIthVar(dd, varIndex);
  Cudd_Ref(var);
  
  DdNode* notVar = Cudd_Not(var);
  Cudd_Ref(notVar);
  
  // Compute cofactors
  DdNode* cofactor1 = Cudd_Cofactor(dd, func, var);
  Cudd_Ref(cofactor1);
  DdNode* cofactor0 = Cudd_Cofactor(dd, func, notVar);
  Cudd_Ref(cofactor0);
  
  // Find cube where cofactor increases from 0 to 1 (positive influence)
  DdNode* increaseRegion = Cudd_bddAnd(dd, Cudd_Not(cofactor0), cofactor1);
  Cudd_Ref(increaseRegion);
  
  // Find cube where cofactor decreases from 1 to 0 (negative influence)
  DdNode* decreaseRegion = Cudd_bddAnd(dd, cofactor0, Cudd_Not(cofactor1));
  Cudd_Ref(decreaseRegion);
  
  bool found = false;
  
  if (increaseRegion != Cudd_ReadLogicZero(dd) && 
      decreaseRegion != Cudd_ReadLogicZero(dd)) {
    
    // Extract assignment from increase region
    char* assignment1 = new char[Cudd_ReadSize(dd) + 1];
    if (Cudd_bddPickOneCube(dd, increaseRegion, assignment1) == 1) {
      pattern1 = std::string(nPis, '0');
      
      for (int j = 0; j < nPis; j++) {
        if (j == piIndex) {
          pattern1[j] = '-';
        } else if (assignment1[j] == 1) {
          pattern1[j] = '1';
        } else if (assignment1[j] == 0) {
          pattern1[j] = '0';
        } else {
          pattern1[j] = '0'; // Don't care, choose 0
        }
      }
      found = true;
    }
    delete[] assignment1;
    
    // Extract assignment from decrease region
    char* assignment2 = new char[Cudd_ReadSize(dd) + 1];
    if (Cudd_bddPickOneCube(dd, decreaseRegion, assignment2) == 1) {
      pattern2 = std::string(nPis, '0');
      
      for (int j = 0; j < nPis; j++) {
        if (j == piIndex) {
          pattern2[j] = '-';
        } else if (assignment2[j] == 1) {
          pattern2[j] = '1';
        } else if (assignment2[j] == 0) {
          pattern2[j] = '0';
        } else {
          pattern2[j] = '0'; // Don't care, choose 0
        }
      }
    }
    delete[] assignment2;
  }
  
  Cudd_RecursiveDeref(dd, increaseRegion);
  Cudd_RecursiveDeref(dd, decreaseRegion);
  Cudd_RecursiveDeref(dd, cofactor1);
  Cudd_RecursiveDeref(dd, cofactor0);
  Cudd_RecursiveDeref(dd, var);
  Cudd_RecursiveDeref(dd, notVar);
  
  return found;
}

void Lsv_CheckUnateBdd(Abc_Ntk_t* pNtk, int k, int i) {
  // Get the k-th primary output
  Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
  if (!pPo) {
    Abc_Print(-1, "Invalid output index %d\n", k);
    return;
  }
  
  // Get the driver of the primary output (the actual node with the BDD)
  Abc_Obj_t* pNode = Abc_ObjFanin0(pPo);
  
  // // Get the i-th primary input
  // Abc_Obj_t* pPi = Abc_NtkPi(pNtk, i);
  // if (!pPi) {
  //   Abc_Print(-1, "Invalid input index %d\n", i);
  //   return;
  // }
  
  // // Debug: print PI name
  // printf("BDD: Checking output %d (%s) with input %d (%s)\n", 
  //        k, Abc_ObjName(pPo), i, Abc_ObjName(pPi));
  

  // Get BDD manager and function
  DdManager* dd = (DdManager*)pNtk->pManFunc;
  if (!dd) {
    Abc_Print(-1, "BDD manager not available. Please run 'collapse' first.\n");
    return;
  }
  
  DdNode* func = (DdNode*)pNode->pData;
  if (!func) {
    Abc_Print(-1, "BDD not available for this output.\n");
    return;
  }
  
  Cudd_Ref(func);

  // Get BDD id for input i
  int varIndex = -1;
  Abc_Obj_t *pRoot = Abc_ObjFanin0(pPo);
  for (int j = 0; j < Abc_ObjFaninNum(pRoot); j++)
    if (Abc_ObjFaninId(pRoot, j) == i + 1){
      varIndex = j;
      break;
    }

  if(varIndex == -1){
    printf("independent\n");
    return;
  }

  // Get the BDD variable for input i
  DdNode* var = Cudd_bddIthVar(dd, varIndex);
  Cudd_Ref(var);
  
  FILE *f = fopen("/home/unknown/Desktop/code/LSV-PA/src/ext-lsv/log.txt", "w");
  cuddPrintNode(var, f);
  fclose(f);

  // Compute positive and negative cofactors
  DdNode* cofactor1 = Cudd_Cofactor(dd, func, var);
  Cudd_Ref(cofactor1);
  
  DdNode* cofactor0 = Cudd_Cofactor(dd, func, Cudd_Not(var));
  Cudd_Ref(cofactor0);
  
  // Check for independence: f|xi=0 == f|xi=1
  if (cofactor0 == cofactor1) {
    printf("independent\n");
  }
  // Check for positive unate: f|xi=0 <= f|xi=1
  else {
    DdNode* implies = Cudd_bddOr(dd, Cudd_Not(cofactor0), cofactor1);
    Cudd_Ref(implies);
    
    if (implies == Cudd_ReadOne(dd)) {
      printf("positive unate\n");
      Cudd_RecursiveDeref(dd, implies);
    } else {
      Cudd_RecursiveDeref(dd, implies);
      
      // Check for negative unate: f|xi=1 <= f|xi=0
      implies = Cudd_bddOr(dd, Cudd_Not(cofactor1), cofactor0);
      Cudd_Ref(implies);
      
      if (implies == Cudd_ReadOne(dd)) {
        printf("negative unate\n");
        Cudd_RecursiveDeref(dd, implies);
      } else {
        Cudd_RecursiveDeref(dd, implies);
        
        // Binate - find counterexample patterns
        printf("binate\n");
        
        std::string pattern1, pattern2;
        int nPis = Abc_NtkPiNum(pNtk);
        
        if (Lsv_FindBinateCube(dd, func, varIndex, nPis, varIndex, pattern1, pattern2)) {
          printf("%s\n", pattern1.c_str());
          printf("%s\n", pattern2.c_str());
        }
      }
    }
  }
  
  Cudd_RecursiveDeref(dd, cofactor1);
  Cudd_RecursiveDeref(dd, cofactor0);
  Cudd_RecursiveDeref(dd, var);
  Cudd_RecursiveDeref(dd, func);
}

int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, i, k;
  
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage_lsv_unate_bdd;
      default:
        goto usage_lsv_unate_bdd;
    }
  }
  
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  
  // Check if network has BDD
  if (!Abc_NtkIsBddLogic(pNtk)) {
    Abc_Print(-1, "Network is not in BDD form. Please run 'collapse' first.\n");
    return 1;
  }
  
  // Parse k and i from remaining arguments
  if (argc - globalUtilOptind != 2) {
    Abc_Print(-1, "Wrong number of arguments.\n");
    goto usage_lsv_unate_bdd;
  }
  
  k = atoi(argv[globalUtilOptind]);
  i = atoi(argv[globalUtilOptind + 1]);
  
  // Validate indices
  if (k < 0 || k >= Abc_NtkPoNum(pNtk)) {
    Abc_Print(-1, "Output index %d is out of range [0, %d)\n", k, Abc_NtkPoNum(pNtk));
    return 1;
  }
  
  if (i < 0 || i >= Abc_NtkPiNum(pNtk)) {
    Abc_Print(-1, "Input index %d is out of range [0, %d)\n", i, Abc_NtkPiNum(pNtk));
    return 1;
  }
  
  Lsv_CheckUnateBdd(pNtk, k, i);
  return 0;

usage_lsv_unate_bdd:
  Abc_Print(-2, "usage: lsv_unate_bdd <k> <i> [-h]\n");
  Abc_Print(-2, "\t        checks unateness of output k with respect to input i using BDD\n");
  Abc_Print(-2, "\t<k>   : primary output index (starting from 0)\n");
  Abc_Print(-2, "\t<i>   : primary input index (starting from 0)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}



/* Exercise 2 : Unateness checking with SAT */

void Lsv_CheckUnateSat(Abc_Ntk_t* pNtk, int k, int i) {
  // Get the k-th primary output
  Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
  if (!pPo) {
    Abc_Print(-1, "Invalid output index %d\n", k);
    return;
  }
  
  // Get the i-th primary input
  Abc_Obj_t* pPi = Abc_NtkPi(pNtk, i);
  if (!pPi) {
    Abc_Print(-1, "Invalid input index %d\n", i);
    return;
  }

  
  // // Debug: print PI name
  // char* piName = Abc_ObjName(pPi);
  // printf("SAT: Checking output %d (%s) with input %d (%s)\n", 
  //        k, Abc_ObjName(pPo), i, piName);
  
  // Step 1: Create cone of yk
  Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 1);
  if (!pCone) {
    Abc_Print(-1, "Failed to create cone\n");
    return;
  }
  
  // Step 2: Convert to AIG
  Aig_Man_t* pMan = Abc_NtkToDar(pCone, 0, 0);
  if (!pMan) {
    Abc_Print(-1, "Failed to convert to AIG\n");
    Abc_NtkDelete(pCone);
    return;
  }
  
  // Step 3: Initialize SAT solver
  sat_solver* pSat = sat_solver_new();
  
  // Step 4: Derive CNF for first copy (CA)
  Cnf_Dat_t* pCnfA = Cnf_Derive(pMan, 1);
  
  // Step 5: Add CNF A to solver
  Cnf_DataWriteIntoSolverInt(pSat, pCnfA, 1, 0);
  
  // Step 6: Create lifted CNF for second copy (CB)
  // Derive a second CNF and lift it
  Cnf_Dat_t* pCnfB = Cnf_Derive(pMan, 1);
  Cnf_DataLift(pCnfB, pCnfA->nVars);
  Cnf_DataWriteIntoSolverInt(pSat, pCnfB, 1, 0);
  
  // Step 7: Find CNF variables for input xi in both copies
  Abc_Obj_t* pPiInCone = Abc_NtkPi(pCone, i);
  if (!pPiInCone) {
    // Input i is not in the cone - it's independent
    printf("independent\n");
    sat_solver_delete(pSat);
    Cnf_DataFree(pCnfA);
    Cnf_DataFree(pCnfB);
    Aig_ManStop(pMan);
    Abc_NtkDelete(pCone);
    return;
  }
  
  // Find corresponding AIG objects
  Aig_Obj_t* pObjPi = Aig_ManCi(pMan, i);
  int varA_i = pCnfA->pVarNums[Aig_ObjId(pObjPi)];
  int varB_i = pCnfB->pVarNums[Aig_ObjId(pObjPi)];
  
  // Find output variable
  Aig_Obj_t* pObjPo = Aig_ManCo(pMan, 0);
  int varA_out = pCnfA->pVarNums[Aig_ObjId(Aig_ObjFanin0(pObjPo))];
  int varB_out = pCnfB->pVarNums[Aig_ObjId(Aig_ObjFanin0(pObjPo))];
  
  // Add clauses to make all inputs except xi equal between A and B
  int nPis = Abc_NtkPiNum(pCone);
  for (int j = 0; j < nPis; j++) {
    if (j == i) continue; // Skip variable of interest
    
    Aig_Obj_t* pObj = Aig_ManCi(pMan, j);
    int varA = pCnfA->pVarNums[Aig_ObjId(pObj)];
    int varB = pCnfB->pVarNums[Aig_ObjId(pObj)];
    
    // Add clauses: varA <=> varB (i.e., (varA => varB) AND (varB => varA))
    lit Lits[2];
    // varA => varB: !varA OR varB
    Lits[0] = toLitCond(varA, 1);
    Lits[1] = toLitCond(varB, 0);
    sat_solver_addclause(pSat, Lits, Lits + 2);
    
    // varB => varA: !varB OR varA
    Lits[0] = toLitCond(varB, 1);
    Lits[1] = toLitCond(varA, 0);
    sat_solver_addclause(pSat, Lits, Lits + 2);
  }
  
  // Check for positive unate: !(fA=0 AND fB=1) is unsat
  // Equivalently: check if fA=0 AND fB=1 is unsat
  lit assumptions[4];
  assumptions[0] = toLitCond(varA_i, 1);  // xi_A = 0
  assumptions[1] = toLitCond(varB_i, 0);  // xi_B = 1
  assumptions[2] = toLitCond(varA_out, 1); // fA = 0
  assumptions[3] = toLitCond(varB_out, 0); // fB = 1
  
  int statusPos = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
  
  // Check for negative unate: !(fA=1 AND fB=0) is unsat
  assumptions[0] = toLitCond(varA_i, 1);  // xi_A = 0
  assumptions[1] = toLitCond(varB_i, 0);  // xi_B = 1
  assumptions[2] = toLitCond(varA_out, 0); // fA = 1
  assumptions[3] = toLitCond(varB_out, 1); // fB = 0
  
  int statusNeg = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
  
  if (statusPos == l_False && statusNeg == l_False) {
    // Both violations are unsat, so function is independent
    printf("independent\n");
  } else if (statusPos == l_False) {
    // Positive unate violation is unsat, so it's positive unate
    printf("positive unate\n");
  } else if (statusNeg == l_False) {
    // Negative unate violation is unsat, so it's negative unate
    printf("negative unate\n");
  } else {
    // Both violations are possible, so it's binate
    printf("binate\n");
    
    // Find pattern 1: where f increases from 0 to 1
    assumptions[0] = toLitCond(varA_i, 1);  // xi_A = 0
    assumptions[1] = toLitCond(varB_i, 0);  // xi_B = 1
    assumptions[2] = toLitCond(varA_out, 1); // fA = 0
    assumptions[3] = toLitCond(varB_out, 0); // fB = 1
    
    int status1 = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
    if (status1 == l_True) {
      std::string pattern(nPis, '0');
      for (int j = 0; j < nPis; j++) {
        if (j == i) {
          pattern[j] = '-';
        } else {
          Aig_Obj_t* pObj = Aig_ManCi(pMan, j);
          int var = pCnfA->pVarNums[Aig_ObjId(pObj)];
          int value = sat_solver_var_value(pSat, var);
          pattern[j] = value ? '1' : '0';
        }
      }
      printf("%s\n", pattern.c_str());
    }
    
    // Find pattern 2: where f decreases from 1 to 0
    assumptions[0] = toLitCond(varA_i, 1);  // xi_A = 0
    assumptions[1] = toLitCond(varB_i, 0);  // xi_B = 1
    assumptions[2] = toLitCond(varA_out, 0); // fA = 1
    assumptions[3] = toLitCond(varB_out, 1); // fB = 0
    
    int status2 = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
    if (status2 == l_True) {
      std::string pattern(nPis, '0');
      for (int j = 0; j < nPis; j++) {
        if (j == i) {
          pattern[j] = '-';
        } else {
          Aig_Obj_t* pObj = Aig_ManCi(pMan, j);
          int var = pCnfA->pVarNums[Aig_ObjId(pObj)];
          int value = sat_solver_var_value(pSat, var);
          pattern[j] = value ? '1' : '0';
        }
      }
      printf("%s\n", pattern.c_str());
    }
  }
  
  // Cleanup
  sat_solver_delete(pSat);
  Cnf_DataFree(pCnfA);
  Cnf_DataFree(pCnfB);
  Aig_ManStop(pMan);
  Abc_NtkDelete(pCone);
}

int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, i, k;
  
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage_lsv_unate_sat;
      default:
        goto usage_lsv_unate_sat;
    }
  }
  
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  
  // Check if network is strashed (AIG)
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not strashed. Please run 'strash' first.\n");
    return 1;
  }
  
  // Parse k and i from remaining arguments
  if (argc - globalUtilOptind != 2) {
    Abc_Print(-1, "Wrong number of arguments.\n");
    goto usage_lsv_unate_sat;
  }
  
  k = atoi(argv[globalUtilOptind]);
  i = atoi(argv[globalUtilOptind + 1]);
  
  // Validate indices
  if (k < 0 || k >= Abc_NtkPoNum(pNtk)) {
    Abc_Print(-1, "Output index %d is out of range [0, %d)\n", k, Abc_NtkPoNum(pNtk));
    return 1;
  }
  
  if (i < 0 || i >= Abc_NtkPiNum(pNtk)) {
    Abc_Print(-1, "Input index %d is out of range [0, %d)\n", i, Abc_NtkPiNum(pNtk));
    return 1;
  }
  
  Lsv_CheckUnateSat(pNtk, k, i);
  return 0;

usage_lsv_unate_sat:
  Abc_Print(-2, "usage: lsv_unate_sat <k> <i> [-h]\n");
  Abc_Print(-2, "\t        checks unateness of output k with respect to input i using SAT\n");
  Abc_Print(-2, "\t<k>   : primary output index (starting from 0)\n");
  Abc_Print(-2, "\t<i>   : primary input index (starting from 0)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}