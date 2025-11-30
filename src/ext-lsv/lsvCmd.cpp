// src/ext-lsv/lsvCmd.cpp
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include "bdd/cudd/cuddInt.h"
#include "bdd/extrab/extraBdd.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "misc/util/abc_global.h"
extern "C" {
    Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

#include <map>
#include <set>
#include <vector>
#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <algorithm>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
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

  // Expanded form of Abc_NtkForEachNode(pNtk, pObj, i)
  for (i = 0; (i < Vec_PtrSize((pNtk)->vObjs)) && (((pObj) = Abc_NtkObj(pNtk, i)), 1); i++) 
  {
    if ((pObj) == NULL || !Abc_ObjIsNode(pObj)) {
      // Skip non-node objects
    } else {
      // Print node ID and name
      printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));

      // Iterate over fanins of this node
      Abc_Obj_t* pFanin;
      int j;
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
               Abc_ObjName(pFanin));
      }

      // Print SOP if the network supports it
      if (Abc_NtkHasSop(pNtk)) {
        printf("The SOP of this node:\n%s", (char*)pObj->pData);
      }
    }
  }
}

void Lsv_NtkPrintMoCut(Abc_Ntk_t* pNtk, int k, int l) {
    Abc_Obj_t* pObj;
    int i;

    // Map: Node ID -> set of fanin Node ID
    std::map<int, std::vector<std::set<int>>> nodeCuts;
    // Map: fanin set -> list of node ids
    std::map<std::set<int>, std::set<int>> cutMap;

    Abc_NtkForEachPi(pNtk, pObj, i) {
        int nodeId = Abc_ObjId(pObj);
        nodeCuts[nodeId].push_back({nodeId});
        cutMap[{nodeId}].insert(nodeId);
    }

    Abc_NtkForEachNode(pNtk, pObj, i) {
        int nodeId = Abc_ObjId(pObj);
        Abc_Obj_t* fanin0 = Abc_ObjFanin0(pObj);
        Abc_Obj_t* fanin1 = Abc_ObjFanin1(pObj);
        int FaninId0 = Abc_ObjId(fanin0);
        int FaninId1 = Abc_ObjId(fanin1);

        const auto& cuts0 = nodeCuts[FaninId0];
        const auto& cuts1 = nodeCuts[FaninId1];

        std::vector<std::set<int>> newCuts;

        for (const auto& c0 : cuts0) {
            for (const auto& c1 : cuts1) {
                std::set<int> merged = c0;
                merged.insert(c1.begin(), c1.end());
                if (merged.size() <= k)
                    newCuts.push_back(merged);
            }
        }

        std::set<int> trivial = {FaninId0, FaninId1};
        if (trivial.size() <= k)
            newCuts.push_back(trivial);

        std::set<int> selfCut = {nodeId};
        newCuts.push_back(selfCut);

        std::vector<std::set<int>> irredundant;
        for (auto& c : newCuts) {
            bool redundant = false;
            for (auto& other : irredundant) {
                if (std::includes(c.begin(), c.end(), other.begin(), other.end())) {
                    redundant = true;
                    break;
                }
            }
            if (!redundant) irredundant.push_back(c);
        }

        nodeCuts[nodeId] = irredundant;

        for (const auto& c : irredundant) {
            cutMap[c].insert(nodeId);
        }
    }

    for (const auto& [cutInputs, nodes] : cutMap) {
        if (cutInputs.size() <= k && nodes.size() >= l) {
            bool first = true;
            for (int id : cutInputs) {
                if (!first) printf(" ");
                printf("%d", id);
                first = false;
            }

            printf(" : ");

            first = true;
            for (int id : nodes) {
                if (!first) printf(" ");
                printf("%d", id);
                first = false;
            }

            printf("\n");
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


int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;

  // Parse integers
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);

  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage_cut;
      default:
        goto usage_cut;
    }
  }

  if (argc < 3) {
    Abc_Print(-1, "Error: lsv_printmocut requires two integer arguments <k> <l>.\n");
    goto usage_cut;
  }

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  // Call your function
  Lsv_NtkPrintMoCut(pNtk, k, l);

  return 0;

usage_cut:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
  Abc_Print(-2, "\t        prints the min-cuts with parameters k and l\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

void PrintPattern(DdManager* dd, DdNode* cube, int xi, int nPis) {
    // 建立 vars array
    DdNode** vars = new DdNode*[nPis];
    for (int j = 0; j < nPis; j++)
        vars[j] = Cudd_bddIthVar(dd, j);

    // 拿一個 minterm
    DdNode* minterm = Cudd_bddPickOneMinterm(dd, cube, vars, nPis);
    Cudd_Ref(minterm);

    for (int j = 0; j < nPis; j++) {
        if (j == xi) {
            printf("-");
        } else {
            // 判斷該 PI 在 minterm 中是 0 還是 1
            int val;
            DdNode* var = Cudd_bddIthVar(dd, j);
            DdNode* f0 = Cudd_Cofactor(dd, minterm, Cudd_Not(var));
            Cudd_Ref(f0);
            if (f0 == Cudd_ReadLogicZero(dd))
                val = 1;
            else
                val = 0;
            printf("%d", val);
            Cudd_RecursiveDeref(dd, f0);
        }
    }
    printf("\n");

    Cudd_RecursiveDeref(dd, minterm);
    delete[] vars;
}



int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (argc < 3) {
    Abc_Print(-2, "usage: lsv_unate_bdd <k> <i>\n");
    return 1;
  }

  int k = atoi(argv[1]); // PO index
  int i = atoi(argv[2]); // PI index

  // printf("[DEBUG] Requested PO = %d, PI = %d\n", k, i);

  // Build global BDDs
  DdManager* dd = (DdManager*)Abc_NtkBuildGlobalBdds(pNtk, 10000000, 1, 1, 0, 0);
  if (dd == NULL) {
    Abc_Print(-1, "Failed to build global BDDs (run collapse first?).\n");
    return 1;
  }

  // printf("[DEBUG] Global BDDs built.\n");
  // printf("[DEBUG] BDD node count = %d\n", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd));

  // Get PO
  Abc_Obj_t* pPo = Abc_NtkCo(pNtk, k);
  if (pPo == NULL) {
    Abc_Print(-1, "PO index %d out of range.\n", k);
    Abc_NtkFreeGlobalBdds(pNtk, 1);
    return 1;
  }

  // Retrieve PO's BDD
  DdNode* bddF = (DdNode*)Abc_ObjGlobalBdd(pPo);
  if (bddF == NULL) {
    Abc_Print(-1, "PO %d has NULL BDD.\n", k);
    Abc_NtkFreeGlobalBdds(pNtk, 1);
    return 1;
  }
  Cudd_Ref(bddF);

  // printf("[DEBUG] F (PO %d) BDD referenced. Node count now = %d\n", k, Cudd_ReadKeys(dd) - Cudd_ReadDead(dd));

  // PI index check
  int nPis = Abc_NtkPiNum(pNtk);
  if (i < 0 || i >= nPis) {
    Abc_Print(-1, "PI index %d out of range.\n", i);
    Cudd_RecursiveDeref(dd, bddF);
    Abc_NtkFreeGlobalBdds(pNtk, 1);
    return 1;
  }

  // Get BDD variable for PI i
  DdNode* var = Cudd_bddIthVar(dd, i);
  Cudd_Ref(var);

  // rintf("[DEBUG] Using BDD variable index %d\n", i);

  // Cofactors
  DdNode* f1 = Cudd_Cofactor(dd, bddF, var);
  Cudd_Ref(f1);
  // printf("[DEBUG] Cofactor f1 = F|xi=1 created. Nodes = %d\n", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd));

  DdNode* nvar = Cudd_Not(var);
  DdNode* f0 = Cudd_Cofactor(dd, bddF, nvar);
  Cudd_Ref(f0);
  // printf("[DEBUG] Cofactor f0 = F|xi=0 created. Nodes = %d\n", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd));

  // Check independence
  DdNode* diff = Cudd_bddXor(dd, f0, f1);
  Cudd_Ref(diff);
  // printf("[DEBUG] XOR(f0,f1) node count = %d\n", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd));

  if (diff == Cudd_ReadLogicZero(dd)) {
    printf("independent\n");
  } else {
    // check positive unate: f0 => f1
    DdNode* notf1 = Cudd_Not(f1); Cudd_Ref(notf1);
    DdNode* t = Cudd_bddAnd(dd, f0, notf1); Cudd_Ref(t);

    // printf("[DEBUG] Checking positive unate, nodes = %d\n", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd));

    if (t == Cudd_ReadLogicZero(dd)) {
      printf("positive unate\n");
    } else {
      Cudd_RecursiveDeref(dd, t);
      DdNode* notf0 = Cudd_Not(f0); Cudd_Ref(notf0);
      DdNode* t2 = Cudd_bddAnd(dd, f1, notf0); Cudd_Ref(t2);

      // printf("[DEBUG] Checking negative unate, nodes = %d\n", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd));

      if (t2 == Cudd_ReadLogicZero(dd)) {
        printf("negative unate\n");
      } else {
        printf("binate\n");
        // printf("[DEBUG] Binate variable detected. Extracting patterns…\n");

        // Pattern 1: want f0 = 0 and f1 = 1
        DdNode* f0_zero = Cudd_Not(f0); Cudd_Ref(f0_zero);
        DdNode* f1_one  = f1;           Cudd_Ref(f1_one);

        DdNode* pattern1 = Cudd_bddAnd(dd, f0_zero, f1_one);
        Cudd_Ref(pattern1);

        // printf("Pattern 1 (f = xi): ");
        PrintPattern(dd, pattern1, i, nPis);

        Cudd_RecursiveDeref(dd, f0_zero);
        Cudd_RecursiveDeref(dd, f1_one);
        Cudd_RecursiveDeref(dd, pattern1);

        // Pattern 2: want f0 = 1 and f1 = 0
        DdNode* f0_one  = f0;           Cudd_Ref(f0_one);
        DdNode* f1_zero = Cudd_Not(f1); Cudd_Ref(f1_zero);

        DdNode* pattern2 = Cudd_bddAnd(dd, f0_one, f1_zero);
        Cudd_Ref(pattern2);

        // printf("Pattern 2 (f = ¬xi): ");
        PrintPattern(dd, pattern2, i, nPis);

        Cudd_RecursiveDeref(dd, f0_one);
        Cudd_RecursiveDeref(dd, f1_zero);
        Cudd_RecursiveDeref(dd, pattern2);
      }
      Cudd_RecursiveDeref(dd, t2);
      Cudd_RecursiveDeref(dd, notf0);
    }

    Cudd_RecursiveDeref(dd, notf1);
  }

  // Cleanup
  Cudd_RecursiveDeref(dd, diff);
  Cudd_RecursiveDeref(dd, f0);
  Cudd_RecursiveDeref(dd, f1);
  Cudd_RecursiveDeref(dd, var);
  Cudd_RecursiveDeref(dd, bddF);

  // printf("[DEBUG] Cleanup done.\n");

  // Free BDDs
  Abc_NtkFreeGlobalBdds(pNtk, 1);

  // printf("[DEBUG] Finished lsv_unate_bdd.\n");

  return 0;
}


int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (argc < 3) {
        Abc_Print(-2, "usage: lsv_unate_sat <k> <i>\n");
        return 1;
    }

    int k = atoi(argv[1]); // PO index
    int i = atoi(argv[2]); // PI index

    // Abc_Print(-2, "=== lsv_unate_sat: start (PO=%d, PI=%d) ===\n", k, i);

    if (k < 0 || k >= Abc_NtkPoNum(pNtk)) {
      Abc_Print(-1, "PO index %d out of range (0..%d)\n", k, Abc_NtkPoNum(pNtk)-1);
      return 1;
    }

    // ensure network is strashed (AIG)
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "Network must be strashed (run \"strash\").\n");
        return 1;
    }

    // get PO
    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
    if (!pPo) {
        Abc_Print(-1, "PO index %d out of range (0..%d)\n", k, Abc_NtkPoNum(pNtk)-1);
        return 1;
    }

    // get the driver (fanin) of the PO: this is the node we should pass to CreateCone
    Abc_Obj_t* pNode = Abc_ObjFanin0(pPo);
    if (!pNode) {
        Abc_Print(-1, "PO %d has no fanin node.\n", k);
        return 1;
    }

    // prepare a safe node name string (don't pass NULL)
    const char* nodeName = Abc_ObjName(pNode);
    char nodeNameBuf[128];
    if (nodeName == NULL) {
        // fallback
        snprintf(nodeNameBuf, sizeof(nodeNameBuf), "po_%d", k);
        nodeName = nodeNameBuf;
    }

    // Abc_Print(-2, "Creating cone for PO %d (driver id=%d, name=%s)\n", k, Abc_ObjId(pNode), nodeName);
    // 1) create cone for PO k (keep all CIs so mapping is stable -> last param = 1)
    Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, pNode, (char*)nodeName, 1);
    if (!pCone) {
        Abc_Print(-1, "Failed to create cone for PO %d (node id %d)\n", k, Abc_ObjId(pNode));
        return 1;
    }
    // Abc_Print(-2, "Cone created. #CIs = %d, #COs = %d\n", Abc_NtkCiNum(pCone), Abc_NtkCoNum(pCone));

    // 2) convert cone to AIG (Dar)
    // Abc_Print(-2, "Converting cone to AIG...\n");
    Aig_Man_t* pAig = Abc_NtkToDar(pCone, 0, 0);
    if (!pAig) {
        Abc_Print(-1, "Failed to convert cone to AIG\n");
        Abc_NtkDelete(pCone);
        return 1;
    }
    // Abc_Print(-2, "AIG created. #CIs (AIG) = %d, #COs (AIG) = %d, #Ands = %d\n", Aig_ManCiNum(pAig), Aig_ManCoNum(pAig), Aig_ManAndNum(pAig));

    // 3) derive CNF for AIG (CA) and a second copy (CB)
    // Abc_Print(-2, "Deriving CNF A (original)...\n");
    Cnf_Dat_t* pCnfA = Cnf_Derive(pAig, Aig_ManCoNum(pAig));


    // 6) map PI (CI) variables between CA and CB and add equalities vA(t) = vB(t) for t != i
    int nPis = Aig_ManCiNum(pAig);
    
    int* pV_A  = ABC_CALLOC(int, Aig_ManObjNumMax(pAig));
    // int* pV_A = (int*) malloc(sizeof(int) * Aig_ManObjNumMax(pAig));
    for (int x = 0; x < Aig_ManObjNumMax(pAig); ++x)
      pV_A[x] = pCnfA->pVarNums[x];    // initialize



      // 4) create SAT solver and add CA
    sat_solver* pSat = sat_solver_new();
    int nVarsA = pCnfA->nVars;
    sat_solver_setnvars(pSat, 2 * nVarsA);
    Cnf_DataWriteIntoSolverInt(pSat, pCnfA, 1, 0);

    // 5) lift CNF B by nVarsA so its vars occupy a different index range, then add to solver
    Cnf_DataLift(pCnfA, nVarsA);
    Cnf_DataWriteIntoSolverInt(pSat, pCnfA, 1, 0);

    for (int t = 0; t < nPis; ++t) {
        if (t == i) {
          // Abc_Print(-2, "  skipping PI %d (the tested variable)\n", i);
          continue;
        }
        Aig_Obj_t* pAigCi = Aig_ManCi(pAig, t);

        int vA = pV_A[Aig_ObjId(pAigCi)]; 
        int vB = pCnfA->pVarNums[Aig_ObjId(pAigCi)];
        // Abc_Print(-2, " PI %2d: AIG CI id=%d -> vA=%d, vB=%d\n", t, Aig_ObjId(pAigCi), vA, vB);

        lit a_pos = toLitCond(vA, 0);
        lit a_neg = toLitCond(vA, 1);
        lit b_pos = toLitCond(vB, 0);
        lit b_neg = toLitCond(vB, 1);

        lit literals[2];

        // A => B
        literals[0] = a_neg; // A'
        literals[1] = b_pos; // B
        sat_solver_addclause(pSat, literals, literals + 2);

        // B => A
        literals[0] = b_neg; // B'
        literals[1] = a_pos; // A
        sat_solver_addclause(pSat, literals, literals + 2);
    }

    // 7) Determine variable indices for y in CA and CB (assume single CO)
    Aig_Obj_t* pAigCo = Aig_ManCo(pAig, 0); // CO object
    Aig_Obj_t* pAigOut  = Aig_ObjFanin0(pAigCo);
    int yA = pV_A[Aig_ObjId(pAigOut)];
    lit litYA = toLitCond(yA, Abc_ObjFaninC0(pPo) ^ Aig_ObjFaninC0(pAigCo));
    int yB = pCnfA->pVarNums[Aig_ObjId(pAigOut)];
    lit litYB = toLitCond(yB, Abc_ObjFaninC0(pPo) ^ Aig_ObjFaninC0(pAigCo));
    // Abc_Print(-2, "Output mapping: AIG CO id=%d -> yA=%d, yB=%d\n", Aig_ObjId(pAigOut), yA, yB);

    // int xi_A = 0;
    // int xi_B = 0;
    // Helper arrays for assumptions
    lit assumptions[4];
    Aig_Obj_t* pObj_xi = Aig_ManCi(pAig, i);
    int xi_A = pV_A[Aig_ObjId(pObj_xi)];
    int xi_B = pCnfA->pVarNums[Aig_ObjId(pObj_xi)];
    assumptions[0] = toLitCond(xi_A, 1);
    assumptions[1] = toLitCond(xi_B, 0);
    std::vector<int> p1, p2;
    int v_temp = 0;

    // Check 1: yA = 0, yB = 1
    assumptions[2] = lit_neg(litYA);
    assumptions[3] = litYB; 
    // Abc_Print(-2, "Assumptions before case1 solve: (%d, %d, %d, %d)\n",
    //       assumptions[0], assumptions[1], assumptions[2], assumptions[3]);
    int status1 = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
    // Abc_Print(-2, "status1 = %d\n", status1);
    if (status1 == l_True) 
      for (int x = 0; x < nPis; ++x) {
            if (x == i) {
              p1.push_back(-1);
            } else {
              v_temp = pV_A[Aig_ObjId(Aig_ManCi(pAig, x))];
              int val = sat_solver_var_value(pSat, v_temp);
              p1.push_back(val ? 1 : 0);
            }
        }


    // Check 1: yA = 1, yB = 0
    assumptions[2] = litYA;
    assumptions[3] = lit_neg(litYB); 
    // Abc_Print(-2, "Assumptions before case2 solve: (%d, %d, %d, %d)\n",
    //       assumptions[0], assumptions[1], assumptions[2], assumptions[3]);
    int status2 = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
    // Abc_Print(-2, "status2 = %d\n", status2);
    if (status2 == l_True) 
      for (int x = 0; x < nPis; ++x) {
            if (x == i) {
              p2.push_back(-1);
            } else {
              v_temp = pV_A[Aig_ObjId(Aig_ManCi(pAig, x))];
              int val = sat_solver_var_value(pSat, v_temp);
              p2.push_back(val ? 1 : 0);
            }
        }

    // Interpret results
    if (status1 == l_True && status2 == l_True) {
        // both satisfiable -> binate
        Abc_Print(-2, "Result: binate\n");
        // Abc_Print(-2, "status1 = %d, status2 = %d\n", status1, status2);
        // 印出時統一處理
        for (int x = 0; x < nPis; ++x) {
            if (p1[x] == -1) printf("-");
            else printf("%d", p1[x]);
        }
        printf("\n");
        for (int x = 0; x < nPis; ++x) {
            if (p2[x] == -1) printf("-");
            else printf("%d", p2[x]);
        }
        printf("\n");
    }
    else if (status1 == l_True && status2 != l_True) {
        // Abc_Print(-2, "Only status1 true -> one direction satisfiable. Interpreting as positive unate (CHECK semantics!)\n");
        printf("positive unate\n");
    }
    else if (status2 == l_True && status1 != l_True) {
        // Abc_Print(-2, "Only status2 true -> one direction satisfiable. Interpreting as negative unate (CHECK semantics!)\n");
        printf("negative unate\n");
    }
    else if (status1 == l_False && status2 == l_False) {
        // Abc_Print(-2, "Neither status1 nor status2 satisfiable -> independent\n");
        printf("independent\n");
    }
    else {
        // Abc_Print(-2, "Unexpected solver result (undef)\n");
        printf("undefined\n");
    }

    // cleanup
    // Abc_Print(-2, "Cleaning up: freeing solver, cnf, aig, cone\n");
    sat_solver_delete(pSat);
    Cnf_DataFree(pCnfA);
    // Cnf_DataFree(pCnfB);
    Aig_ManStop(pAig);
    Abc_NtkDelete(pCone);

    // Abc_Print(-2, "=== lsv_unate_sat: done ===\n");
    return 0;
}