#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/extrab/extraBdd.h"
#include "bdd/cudd/cudd.h"
#include "sat/cnf/cnf.h"
#include <set>
#include <map>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintmocut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

extern "C" {Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );}

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintmocut, 0);
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

void enumerate_k_feasible_cuts(Abc_Obj_t* pObj, int k, std::map<int, std::set<std::set<int>>>& nodeIDtoCuts){
  int id = Abc_ObjId(pObj);
  if(nodeIDtoCuts.find(id) != nodeIDtoCuts.end()) {
    return; // already computed
  }
  if(Abc_ObjIsPi(pObj)) {
    nodeIDtoCuts[id].insert({id});
    return;
  }
  Abc_Obj_t* pFanin;
  int j;
  Abc_ObjForEachFanin(pObj, pFanin, j) {
    enumerate_k_feasible_cuts(pFanin, k, nodeIDtoCuts);
  }
  
  nodeIDtoCuts[id].insert({id}); // include trivial cut
  // combine cuts from fanins
  for(auto it1 = nodeIDtoCuts[Abc_ObjId(Abc_ObjFanin0(pObj))].begin(); it1 != nodeIDtoCuts[Abc_ObjId(Abc_ObjFanin0(pObj))].end(); ++it1) {
    for(auto it2 = nodeIDtoCuts[Abc_ObjId(Abc_ObjFanin1(pObj))].begin(); it2 != nodeIDtoCuts[Abc_ObjId(Abc_ObjFanin1(pObj))].end(); ++it2) {
      std::set<int> combinedCut = *it1;
      combinedCut.insert(it2->begin(), it2->end());
      if(combinedCut.size() <= k) {
        nodeIDtoCuts[id].insert(combinedCut);
      }
    }
  }
}

void map_cuts_to_outputs(std::map<int, std::set<std::set<int>>>& nodeIDtoCuts, std::map<std::set<int>, std::set<int>>& cutToOutputs) {
  for(const auto& pair : nodeIDtoCuts) {
    int nodeId = pair.first;
    const std::set<std::set<int>>& cuts = pair.second;
    for(const auto& cut : cuts) {
      cutToOutputs[cut].insert(nodeId);
    }
  }
}

void Lsv_NtkPrintmocut(Abc_Ntk_t* pNtk, int k, int l) {
  std::map<int, std::set<std::set<int>>> nodeIDtoCuts;
  std::map<std::set<int>, std::set<int>> cutToOutputs;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachObj(pNtk, pObj, i) {
    if(Abc_ObjIsNode(pObj)) {
      // call recursive function to enumerate k-feasible cuts and their outputs
      int id = Abc_ObjId(pObj);
      if(nodeIDtoCuts.find(id) == nodeIDtoCuts.end()) {
        enumerate_k_feasible_cuts(pObj, k, nodeIDtoCuts);
      }
    }
  }
  // iterate nodeIDtoCuts to map cuts to outputs
  map_cuts_to_outputs(nodeIDtoCuts, cutToOutputs);
  // iterate through cutToOutputs to find multi-output cuts
  // output format <in_1> <in_2> ... : <out_1> <out_2> ...
  for(const auto& pair : cutToOutputs) {
    const std::set<int>& leafSet = pair.first;
    const std::set<int>& outputs = pair.second;
    if(outputs.size() >= l) {
      for(const int& leaf : leafSet) {
        printf("%d ", leaf);
      }
      printf(": ");
      for(const int& output : outputs) {
        // the final one should not have a trailing space
        if(output == *outputs.rbegin()) {
          printf("%d", output);
          break;
        }
        printf("%d ", output);
      }
      printf("\n");
    }
  }
}

int Lsv_CommandPrintmocut(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (argc != 3) {
    goto usage;
  }
  int k;
  k = atoi(argv[1]);
  int l;
  l = atoi(argv[2]);

  if(!pNtk){
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintmocut(pNtk, k, l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
  Abc_Print(-2, "\t prints the multioutput k-feasible cuts with at least l outputs\n");
  Abc_Print(-2, "\t -h : print the command usage\n");
  return 1;
}

// ======================================
// PA2
// part1: lsv_unate_bdd

void Lsv_PrintBinatePattern(DdManager * dd, Abc_Ntk_t * pNtk, DdNode * bddFunc, int targetPiIndex) {
    int * cube;
    CUDD_VALUE_TYPE val;
    DdGen * gen; // Ensure this is a pointer
    
    // Safety check: If the BDD function is empty (logical 0), there are no patterns to print
    if (bddFunc == Cudd_ReadLogicZero(dd)) {
        printf("Error: Domain is empty.\n");
        return;
    }

    Cudd_ForeachCube(dd, bddFunc, gen, cube, val) {
        // Inside Lsv_PrintBinatePattern loop
        for (int j = 0; j < Abc_NtkPiNum(pNtk); j++) {
            if (j == targetPiIndex) {
                printf("-");
            }
            else {
                // We need to find which BDD variable corresponds to PI 'j'
                Abc_Obj_t * pPi = Abc_NtkPi(pNtk, j);
                DdNode * piBdd = (DdNode *)pPi->pData;
                int bddVarIdx;

                if (piBdd != NULL) {
                    bddVarIdx = Cudd_Regular(piBdd)->index;
                } else {
                    // Apply the same reverse mapping here!
                    int numPis = Abc_NtkPiNum(pNtk);
                    bddVarIdx = (numPis - 1) - j; 
                }

                // Now lookup the cube using the corrected BDD index
                if (bddVarIdx < 0 || bddVarIdx >= Cudd_ReadSize(dd)) {
                    printf("0");
                } else {
                    if (cube[bddVarIdx] == 1) printf("1");
                    else printf("0");
                }
            }
        }
        printf("\n");
        Cudd_GenFree(gen);
        return; // Print only one pattern
    }
}

int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
    if (argc != 3) {
        Abc_Print(-1, "Usage: lsv_unate_bdd <output_index> <input_index>\n");
        return 1;
    }
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int outputIdx, inputIdx;
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsBddLogic(pNtk)) {
         Abc_Print(-1, "Network is not in BDD format. Run 'collapse' first.\n");
         return 1; 
    }

    outputIdx = atoi(argv[1]);
    inputIdx = atoi(argv[2]);

    if (outputIdx >= Abc_NtkPoNum(pNtk) || inputIdx >= Abc_NtkPiNum(pNtk)) {
        Abc_Print(-1, "Index out of bounds.\n");
        return 1;
    }
    
    DdManager * dd = (DdManager *)pNtk->pManFunc;
    
    Abc_Obj_t * pPo = Abc_NtkPo(pNtk, outputIdx);
    Abc_Obj_t * pPi = Abc_NtkPi(pNtk, inputIdx);
    
    Abc_Obj_t * pRoot = Abc_ObjFanin0(pPo); 

    // Retrieve the BDD from the driving node's data
    DdNode * fn_node = (DdNode *)pRoot->pData;

    // If the wire from the logic node to the PO is inverted, we must complement the BDD.
    if (Abc_ObjFaninC0(pPo)) {
        fn_node = Cudd_Not(fn_node);
    }

    DdNode * var_node;    
    int numPis = Abc_NtkPiNum(pNtk);
    int mappedBddIndex = (numPis - 1) - inputIdx;        
    var_node = Cudd_bddIthVar(dd, mappedBddIndex);

    DdNode * f_pos = Cudd_Cofactor(dd, fn_node, var_node);
    Cudd_Ref(f_pos);
    DdNode * f_neg = Cudd_Cofactor(dd, fn_node, Cudd_Not(var_node));
    Cudd_Ref(f_neg);
    
    // Check Independent: f_pos == f_neg
    if (f_pos == f_neg) {
        printf("independent\n");
    } 
    // Check Positive Unate: f_neg <= f_pos
    else if (Cudd_bddLeq(dd, f_neg, f_pos)) {
        printf("positive unate\n");
    }
    // Check Negative Unate: f_pos <= f_neg
    else if (Cudd_bddLeq(dd, f_pos, f_neg)) {
        printf("negative unate\n");
    }
    else {
        printf("binate\n");

        // Positive behavior witness
        // P1 = f_pos & (!f_neg)
        DdNode * diff_pos = Cudd_bddAnd(dd, f_pos, Cudd_Not(f_neg));
        Cudd_Ref(diff_pos);
        Lsv_PrintBinatePattern(dd, pNtk, diff_pos, inputIdx);
        Cudd_RecursiveDeref(dd, diff_pos);

        // Pattern 2: Negative behavior witness
        // Logic: P2 = (!f_pos) & f_neg
        DdNode * diff_neg = Cudd_bddAnd(dd, Cudd_Not(f_pos), f_neg);
        Cudd_Ref(diff_neg);
        Lsv_PrintBinatePattern(dd, pNtk, diff_neg, inputIdx);
        Cudd_RecursiveDeref(dd, diff_neg);
    }

    Cudd_RecursiveDeref(dd, f_pos);
    Cudd_RecursiveDeref(dd, f_neg);

    return 0;
}

// part2: lsv_unate_sat
void Lsv_PrintSatPattern(sat_solver* pSat, int nPis, int* pVarNumsA, int targetIdx) {
    for (int j = 0; j < nPis; j++) {
        if (j == targetIdx) {
            printf("-");
        } else {
            // Check value of variable pVarNumsA[j] in the solver
            // sat_solver_var_value returns 1 (True) or 0 (False)
            printf("%d", sat_solver_var_value(pSat, pVarNumsA[j]));
        }
    }
    printf("\n");
}

int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
    if (argc != 3) {
        Abc_Print(-1, "Usage: lsv_unate_sat <output_index> <input_index>\n");
        return 1;
    }

    int outIdx = atoi(argv[1]);
    int inIdx = atoi(argv[2]);

    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    
    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, outIdx);
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);
    int isInv = Abc_ObjFaninC0(pPo);

    // Create cone
    Abc_Ntk_t* pNtkCone = Abc_NtkCreateCone(pNtk, pRoot, Abc_ObjName(pRoot), 1);
    Aig_Man_t* pAig = Abc_NtkToDar(pNtkCone, 0, 1);
    Cnf_Dat_t* pCnf = Cnf_Derive(pAig, 1); 

    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars(pSat, pCnf->nVars * 2);

    Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);

    int nPis = Abc_NtkPiNum(pNtk);
    int* pVarNumsA = new int[nPis];
    Aig_Obj_t* pObjAig;
    int k;
    
    Aig_ManForEachCi(pAig, pObjAig, k) {
        pVarNumsA[k] = pCnf->pVarNums[pObjAig->Id];
    }

    Aig_Obj_t* pObjPo = Aig_ManCo(pAig, 0); 
    int varOutA = pCnf->pVarNums[pObjPo->Id]; // map variable for output

    int offset = pCnf->nVars; // shift amount
    Cnf_DataLift(pCnf, offset); // Adjust IDs in pCnf
    Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);

    for (int j = 0; j < nPis; j++) {
        if (j == inIdx) continue;
        int vA = pVarNumsA[j];
        int vB = vA + offset;
        
        // Add constraint: vA == vB
        lit Lits[2];

        // (!vA + vB)
        Lits[0] = toLitCond(vA, 1);
        Lits[1] = toLitCond(vB, 0);
        sat_solver_addclause(pSat, Lits, Lits + 2);

        // (vA + !vB)
        Lits[0] = toLitCond(vA, 0);
        Lits[1] = toLitCond(vB, 1);
        sat_solver_addclause(pSat, Lits, Lits + 2);
    }

    int vInA = pVarNumsA[inIdx];
    int vInB = vInA + offset;
    int vOutB = varOutA + offset;

    // assume xA=0 and xB=1 for the target input in both checks
    lit Lits[4];

    // Note: If isInv is true, logic_node=1 means y=0.
    Lits[0] = toLitCond(vInA, 1);              // xA=0
    Lits[1] = toLitCond(vInB, 0);              // xB=1
    Lits[2] = toLitCond(varOutA, !isInv);      // yA=0 (Node must be !Inv)
    Lits[3] = toLitCond(vOutB, isInv);         // yB=1 (Node must be Inv)
    
    int statusPos = sat_solver_solve(pSat, Lits, Lits + 4, 0, 0, 0, 0);

    // Assumptions: xA=0, xB=1, yA=1, yB=0
    Lits[0] = toLitCond(vInA, 1);              // xA=0
    Lits[1] = toLitCond(vInB, 0);              // xB=1
    Lits[2] = toLitCond(varOutA, isInv);       // yA=1
    Lits[3] = toLitCond(vOutB, !isInv);        // yB=0
    
    int statusNeg = sat_solver_solve(pSat, Lits, Lits + 4, 0, 0, 0, 0);

    if (statusPos == l_False && statusNeg == l_False) {
        printf("independent\n");
    } else if (statusPos == l_True && statusNeg == l_False) {
        // Can rise, cannot fall
        printf("positive unate\n");
    } else if (statusPos == l_False && statusNeg == l_True) {
        // Cannot rise, can fall
        printf("negative unate\n");
    } else {
        printf("binate\n");
        // Print Pattern 1 (Positive Witness: x=0 -> y=0, x=1 -> y=1)
        Lits[0] = toLitCond(vInA, 1);
        Lits[1] = toLitCond(vInB, 0);
        Lits[2] = toLitCond(varOutA, !isInv); 
        Lits[3] = toLitCond(vOutB, isInv);
        sat_solver_solve(pSat, Lits, Lits + 4, 0, 0, 0, 0);
        Lsv_PrintSatPattern(pSat, nPis, pVarNumsA, inIdx);

        // Print Pattern 2 (Negative Witness: x=0 -> y=1, x=1 -> y=0)
        // re-solve for Neg
        Lits[0] = toLitCond(vInA, 1);
        Lits[1] = toLitCond(vInB, 0);
        Lits[2] = toLitCond(varOutA, isInv); 
        Lits[3] = toLitCond(vOutB, !isInv);
        sat_solver_solve(pSat, Lits, Lits + 4, 0, 0, 0, 0);
        Lsv_PrintSatPattern(pSat, nPis, pVarNumsA, inIdx);
    }

    delete [] pVarNumsA;
    Abc_NtkDelete(pNtkCone);
    Cnf_DataFree(pCnf);
    sat_solver_delete(pSat);
    Aig_ManStop(pAig);

    return 0;
}