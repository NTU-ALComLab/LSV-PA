#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "opt/cut/cut.h"

#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"
#endif

#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"

extern "C" {
  Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}

/*===lsv_ext ===============================================================*/
extern ABC_DLL void               Lsv_NtkPrintMOCuts( Abc_Ntk_t * pNtk ,int k, int l);
extern ABC_DLL void               Lsv_NtkPrintUnateBDD( Abc_Ntk_t * pNtk ,int k, int i);
extern ABC_DLL void               Lsv_NtkPrintUnateSAT( Abc_Ntk_t * pNtk ,int k, int i);
//lsv commands ==============================================================
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Abc_CommandLsvPrintMOCut         (Abc_Frame_t * pAbc, int argc, char ** argv);
static int Abc_CommandLsvUnateBdd           (Abc_Frame_t * pAbc, int argc, char ** argv);
static int Abc_CommandLsvUnateSat           (Abc_Frame_t * pAbc, int argc, char ** argv);

/**Function*************************************************************

  Synopsis    []

  Description [initializes the lsv package]

  SideEffects []

  SeeAlso     [Cmd_CommandAdd]

***********************************************************************/
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd( pAbc, "LSV",          "lsv_printmocut", Abc_CommandLsvPrintMOCut,   0 );
  Cmd_CommandAdd( pAbc, "LSV",          "lsv_unate_bdd", Abc_CommandLsvUnateBdd,   0 );
  Cmd_CommandAdd( pAbc, "LSV",          "lsv_unate_sat", Abc_CommandLsvUnateSat,   0 );
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

/**Function*************************************************************

  Synopsis    []

  Description [prints the nodes in the network]

  SideEffects []

  SeeAlso     []

***********************************************************************/
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
/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     [Lsv_NtkPrintMOCuts]

***********************************************************************/

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

/**Function*************************************************************

  Synopsis    []

  Description [prints the k-l multi-output cuts in the network]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CommandLsvPrintMOCut(Abc_Frame_t * pAbc, int argc, char ** argv) {
  int k, l, c;
  Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

  // Check if network exists
  if (pNtk == NULL) {
    Abc_Print( -1, "Empty network.\n");
    return 1;
  }

  // Parse command line options first
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }

  // Check if the correct number of positional arguments are provided
  if (argc != globalUtilOptind + 2) {
    Abc_Print( -1, "Error: Expecting exactly two parameters (k and l).\n");
    goto usage;
  }

  // Parse k parameter
  k = atoi(argv[globalUtilOptind]);
  if (k < 3 || k > 6) {
    Abc_Print( -1, "Error: k must be between 3 and 6 (inclusive).\n");
    return 1;
  }

  // Parse l parameter
  l = atoi(argv[globalUtilOptind + 1]);
  if (l < 1 || l > 4) {
    Abc_Print( -1, "Error: l must be between 1 and 4 (inclusive).\n");
    return 1;
  }

  // Check if network is strashed
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print( -1, "Error: This command works only for AIGs. Please run \"strash\" first.\n");
    return 1;
  }

  // TODO: Implement k-l multi-output cut enumeration
  // Enumerate and print k-l multi-output cuts
  Lsv_NtkPrintMOCuts(pNtk, k, l);

  return 0;

  usage:
    Abc_Print( -2, "usage: lsv_printmocut <k> <l> [-h]\n");
    Abc_Print( -2, "\t        prints the k-l multi-output cuts in the network\n");
    Abc_Print( -2, "\t<k>    : maximum cut size (3 <= k <= 6)\n");
    Abc_Print( -2, "\t<l>    : minimum number of outputs (1 <= l <= 4)\n");
    Abc_Print( -2, "\t-h     : print the command usage\n");
  return 1;
}

int Abc_CommandLsvUnateBdd(Abc_Frame_t * pAbc, int argc, char ** argv) {
  Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
  int k,i,c;

  if (pNtk == NULL) {
    Abc_Print( -1, "Empty network.\n");
    return 1;
  }

  // Parse command line options first
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }

  // Check if the correct number of positional arguments are provided
  if (argc != globalUtilOptind + 2) {
    Abc_Print( -1, "Error: Expecting exactly two parameters (k and l).\n");
    goto usage;
  }

  // Parse k parameter
  k = atoi(argv[globalUtilOptind]);
  // Parse l parameter
  i = atoi(argv[globalUtilOptind + 1]);
  
  Lsv_NtkPrintUnateBDD(pNtk, k, i);

  return 0;
  usage:
  Abc_Print( -2, "usage: lsv_unate_bdd <k> <i> [-h]\n");
  Abc_Print( -2, "\t        checks unateness of output k with respect to input i using BDD\n");
  Abc_Print( -2, "\t<k>    : primary output index (starting from 0)\n");
  Abc_Print( -2, "\t<i>    : primary input index (starting from 0)\n");
  Abc_Print( -2, "\t-h     : print the command usage\n");
  return 1;
}

int Abc_CommandLsvUnateSat(Abc_Frame_t * pAbc, int argc, char ** argv) {
  Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
  int k,i,c;

  if (pNtk == NULL) {
    Abc_Print( -1, "Empty network.\n");
    return 1;
  }

  // Parse command line options first
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }

  // Check if the correct number of positional arguments are provided
  if (argc != globalUtilOptind + 2) {
    Abc_Print( -1, "Error: Expecting exactly two parameters (k and i).\n");
    goto usage;
  }

  // Parse k parameter
  k = atoi(argv[globalUtilOptind]);
  // Parse i parameter
  i = atoi(argv[globalUtilOptind + 1]);
  
  Lsv_NtkPrintUnateSAT(pNtk, k, i);

  return 0;
  usage:
  Abc_Print( -2, "usage: lsv_unate_sat <k> <i> [-h]\n");
  Abc_Print( -2, "\t        checks unateness of output k with respect to input i using SAT\n");
  Abc_Print( -2, "\t<k>    : primary output index (starting from 0)\n");
  Abc_Print( -2, "\t<i>    : primary input index (starting from 0)\n");
  Abc_Print( -2, "\t-h     : print the command usage\n");
  return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     [Lsv_NtkPrintMOCuts]

***********************************************************************/
void Lsv_NtkPrintMOCuts(Abc_Ntk_t* pNtk, int k, int l) {
  Cut_Man_t* pManCut;
  Cut_Params_t Params;
  Cut_Cut_t* pList;
  Abc_Obj_t* pObj;
  int i, j;
  
  // Initialize cut parameters
  memset(&Params, 0, sizeof(Cut_Params_t));
  Params.nVarsMax = k;        // maximum cut size (k-feasible)
  Params.nKeepMax = 1000;     // maximum number of cuts to keep per node
  Params.fTruth = 0;          // don't compute truth tables (not needed for enumeration)
  Params.fFilter = 1;         // filter dominated cuts (keep only irredundant)
  Params.fSeq = 0;            // don't compute sequential cuts
  Params.fDrop = 0;           // don't drop cuts on the fly
  Params.fVerbose = 0;        // no verbose output
  Params.nIdsMax = Abc_NtkObjNumMax(pNtk);
  
  // Start cut manager
  pManCut = Cut_ManStart(&Params);
  if (!pManCut) {
    printf("Error: Failed to start cut manager\n");
    return;
  }
  
  // Set trivial cuts for primary inputs
  Abc_NtkForEachCi(pNtk, pObj, i) {
    if (Abc_ObjFanoutNum(pObj) > 0) {
      Cut_NodeSetTriv(pManCut, pObj->Id);
    }
  }
  
  // Compute cuts for all nodes using DFS traversal
  Vec_Ptr_t* vNodes = Abc_AigDfs(pNtk, 0, 1);
  Vec_PtrForEachEntry(Abc_Obj_t*, vNodes, pObj, i) {
    if (Abc_ObjIsCo(pObj)) {
      continue; // Skip primary outputs
    }
    
    // Compute cuts for this node
    Abc_NodeGetCuts(pManCut, pObj, 0, 0);
  }
  Vec_PtrFree(vNodes);
  
  // Data structure to store multi-output cuts
  // Key: cut signature (sorted list of leaf IDs), Value: list of output nodes
  typedef struct {
    Vec_Int_t* vLeaves;     // sorted leaf IDs
    Vec_Int_t* vOutputs;    // output node IDs that have this cut
  } MultiOutputCut;
  
  Vec_Ptr_t* vMultiCuts = Vec_PtrAlloc(100);
  
  // Collect all cuts and group by cut content
  // Process Primary Inputs
  Abc_NtkForEachCi(pNtk, pObj, i) {
    if (Abc_ObjFanoutNum(pObj) > 0) {
      pList = (Cut_Cut_t*)Abc_NodeReadCuts(pManCut, pObj);
      if (pList) {
        Cut_Cut_t* pCut;
        for (pCut = pList; pCut; pCut = pCut->pNext) {
          if (pCut->nLeaves <= k && pCut->nLeaves > 0) { // k-feasible non-trivial cut
            // Create sorted array of leaf IDs for this cut
            Vec_Int_t* vCutLeaves = Vec_IntAlloc(pCut->nLeaves);
            int idx;
            for (idx = 0; idx < pCut->nLeaves; idx++) {
              Vec_IntPush(vCutLeaves, pCut->pLeaves[idx]);
            }
            Vec_IntSort(vCutLeaves, 0);
            
            // Check if this cut already exists
            MultiOutputCut* pMultiCut = NULL;
            int idx2;
            Vec_PtrForEachEntry(MultiOutputCut*, vMultiCuts, pMultiCut, idx2) {
              if (Vec_IntSize(pMultiCut->vLeaves) == Vec_IntSize(vCutLeaves)) {
                int equal = 1;
                int k;
                for (k = 0; k < Vec_IntSize(vCutLeaves); k++) {
                  if (Vec_IntEntry(pMultiCut->vLeaves, k) != Vec_IntEntry(vCutLeaves, k)) {
                    equal = 0;
                    break;
                  }
                }
                if (equal) {
                  Vec_IntFree(vCutLeaves);
                  Vec_IntPushUnique(pMultiCut->vOutputs, Abc_ObjId(pObj));
                  goto next_cut_pi;
                }
              }
            }
            
            // Create new multi-output cut entry
            pMultiCut = (MultiOutputCut*)malloc(sizeof(MultiOutputCut));
            pMultiCut->vLeaves = vCutLeaves;
            pMultiCut->vOutputs = Vec_IntAlloc(4);
            Vec_IntPush(pMultiCut->vOutputs, Abc_ObjId(pObj));
            Vec_PtrPush(vMultiCuts, pMultiCut);
            
            next_cut_pi:;
          }
        }
      }
    }
  }
  
  // Process AND nodes
  Abc_NtkForEachNode(pNtk, pObj, i) {
    pList = (Cut_Cut_t*)Abc_NodeReadCuts(pManCut, pObj);
    if (pList) {
      Cut_Cut_t* pCut;
      for (pCut = pList; pCut; pCut = pCut->pNext) {
        if (pCut->nLeaves <= k && pCut->nLeaves > 0) { // k-feasible non-trivial cut
          // Create sorted array of leaf IDs for this cut
          Vec_Int_t* vCutLeaves = Vec_IntAlloc(pCut->nLeaves);
          int idx;
          for (idx = 0; idx < pCut->nLeaves; idx++) {
            Vec_IntPush(vCutLeaves, pCut->pLeaves[idx]);
          }
          Vec_IntSort(vCutLeaves, 0);
          
          // Check if this cut already exists
          MultiOutputCut* pMultiCut = NULL;
          int idx2;
          Vec_PtrForEachEntry(MultiOutputCut*, vMultiCuts, pMultiCut, idx2) {
            if (Vec_IntSize(pMultiCut->vLeaves) == Vec_IntSize(vCutLeaves)) {
              int equal = 1;
              int k;
              for (k = 0; k < Vec_IntSize(vCutLeaves); k++) {
                if (Vec_IntEntry(pMultiCut->vLeaves, k) != Vec_IntEntry(vCutLeaves, k)) {
                  equal = 0;
                  break;
                }
              }
              if (equal) {
                Vec_IntFree(vCutLeaves);
                Vec_IntPushUnique(pMultiCut->vOutputs, Abc_ObjId(pObj));
                goto next_cut_and;
              }
            }
          }
          
          // Create new multi-output cut entry
          pMultiCut = (MultiOutputCut*)malloc(sizeof(MultiOutputCut));
          pMultiCut->vLeaves = vCutLeaves;
          pMultiCut->vOutputs = Vec_IntAlloc(4);
          Vec_IntPush(pMultiCut->vOutputs, Abc_ObjId(pObj));
          Vec_PtrPush(vMultiCuts, pMultiCut);
          
          next_cut_and:;
        }
      }
    }
  }
  
  // Print k-l multi-output cuts
  printf("k-l Multi-Output Cuts (k=%d, l=%d):\n", k, l);
  printf("===================================\n");
  
  int multiOutputCutCount = 0;
  MultiOutputCut* pMultiCut;
  Vec_PtrForEachEntry(MultiOutputCut*, vMultiCuts, pMultiCut, i) {
    if (Vec_IntSize(pMultiCut->vOutputs) >= l) {
      multiOutputCutCount++;
      
      /*
      // Print inputs
      printf("Cut %d:\n", multiOutputCutCount);
      printf("  Inputs (%d): {", Vec_IntSize(pMultiCut->vLeaves));
      for (j = 0; j < Vec_IntSize(pMultiCut->vLeaves); j++) {
        if (j > 0) printf(", ");
        int nodeId = Vec_IntEntry(pMultiCut->vLeaves, j);
        Abc_Obj_t* pNode = Abc_NtkObj(pNtk, nodeId);
        printf("%d", Abc_ObjId(pNode));
      }
      printf("}\n");
      
      // Print outputs
      printf("  Outputs (%d): {", Vec_IntSize(pMultiCut->vOutputs));
      for (j = 0; j < Vec_IntSize(pMultiCut->vOutputs); j++) {
        if (j > 0) printf(", ");
        int nodeId = Vec_IntEntry(pMultiCut->vOutputs, j);
        Abc_Obj_t* pNode = Abc_NtkObj(pNtk, nodeId);
        printf("%d", Abc_ObjId(pNode));
      }
      printf("}\n\n");
      */

      // print with requested format
      for(j = 0; j < Vec_IntSize(pMultiCut->vLeaves); j++){
        if (j > 0) printf(" ");
        int nodeId = Vec_IntEntry(pMultiCut->vLeaves, j);
        Abc_Obj_t* pNode = Abc_NtkObj(pNtk, nodeId);
        printf("%d", Abc_ObjId(pNode));
      }
      printf(" : ");
      for(j = 0; j < Vec_IntSize(pMultiCut->vOutputs); j++){
        if (j > 0) printf(" ");
        int nodeId = Vec_IntEntry(pMultiCut->vOutputs, j);
        Abc_Obj_t* pNode = Abc_NtkObj(pNtk, nodeId);
        printf("%d", Abc_ObjId(pNode));
      }
      printf("\n");
    }
  }
  
  //printf("Total %d-%d multi-output cuts: %d\n", k, l, multiOutputCutCount);
  
  // Clean up
  Vec_PtrForEachEntry(MultiOutputCut*, vMultiCuts, pMultiCut, i) {
    Vec_IntFree(pMultiCut->vLeaves);
    Vec_IntFree(pMultiCut->vOutputs);
    free(pMultiCut);
  }
  Vec_PtrFree(vMultiCuts);
  Cut_ManStop(pManCut);
}

/**Function*************************************************************

  Synopsis    [Checks the unateness of output k with respect to input i using BDD.]

  Description [For a BDD logic network (after collapse), checks whether
  the function of primary output k is positive unate, negative unate,
  independent of, or binate in primary input i. If binate, prints two
  patterns demonstrating the binateness.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
#ifdef ABC_USE_CUDD
void Lsv_NtkPrintUnateBDD(Abc_Ntk_t* pNtk, int k, int i) {
  // Validate network type
  if (!Abc_NtkIsBddLogic(pNtk)) {
    Abc_Print(-1, "Error: Network is not a BDD logic network. Please run \"collapse\" first.\n");
    return;
  }

  // Validate output index
  if (k < 0 || k >= Abc_NtkPoNum(pNtk)) {
    Abc_Print(-1, "Error: Output index %d is out of range [0, %d).\n", k, Abc_NtkPoNum(pNtk));
    return;
  }

  // Validate input index
  if (i < 0 || i >= Abc_NtkPiNum(pNtk)) {
    Abc_Print(-1, "Error: Input index %d is out of range [0, %d).\n", i, Abc_NtkPiNum(pNtk));
    return;
  }

  // Get the BDD manager
  DdManager* dd = (DdManager*)pNtk->pManFunc;

  // Get the primary output
  Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
  // Get the driver node (fanin of the PO)
  Abc_Obj_t* pNode = Abc_ObjFanin0(pPo);

  // Get the BDD function of the driver node
  DdNode* bFunc = (DdNode*)pNode->pData;
  Cudd_Ref(bFunc);

  // Get the primary input at index i
  Abc_Obj_t* pPi = Abc_NtkPi(pNtk, i);

  // Find which fanin of the driver node corresponds to this PI
  int faninIndex = -1;
  Abc_Obj_t* pFanin;
  int j;
  Abc_ObjForEachFanin(pNode, pFanin, j) {
    if (pFanin == pPi) {
      faninIndex = j;
      break;
    }
  }

  // If PI is not in the support of this function, it's independent
  if (faninIndex == -1) {
    Abc_Print(1, "independent\n");
    Cudd_RecursiveDeref(dd, bFunc);
    return;
  }

  // Get the BDD variable for this fanin
  DdNode* bVar = Cudd_bddIthVar(dd, faninIndex);

  // Compute positive and negative cofactors
  DdNode* bCof1 = Cudd_Cofactor(dd, bFunc, bVar);
  Cudd_Ref(bCof1);
  DdNode* bCof0 = Cudd_Cofactor(dd, bFunc, Cudd_Not(bVar));
  Cudd_Ref(bCof0);

  // Check unateness using Cudd_bddLeq:
  // - Positive unate: bCof0 <= bCof1 (i.e., f|xi=0 implies f|xi=1)
  // - Negative unate: bCof1 <= bCof0 (i.e., f|xi=1 implies f|xi=0)
  int isPosUnate = Cudd_bddLeq(dd, bCof0, bCof1);
  int isNegUnate = Cudd_bddLeq(dd, bCof1, bCof0);

  if (isPosUnate && isNegUnate) {
    // Both hold means cofactors are equal - function is independent
    Abc_Print(1, "independent\n");
  } else if (isPosUnate) {
    Abc_Print(1, "positive unate\n");
  } else if (isNegUnate) {
    Abc_Print(1, "negative unate\n");
  } else {
    // Binate: need to find two patterns
    // Pattern 1: where f|xi=1 > f|xi=0, i.e., (f|xi=1 AND NOT f|xi=0) is satisfiable
    // Pattern 2: where f|xi=0 > f|xi=1, i.e., (f|xi=0 AND NOT f|xi=1) is satisfiable
    Abc_Print(1, "binate\n");

    int nPis = Abc_NtkPiNum(pNtk);
    char* pCube = ABC_ALLOC(char, dd->size);

    // Create a mapping from PI index to fanin index (-1 if not in support)
    int* piToFanin = ABC_ALLOC(int, nPis);
    for (j = 0; j < nPis; j++) {
      piToFanin[j] = -1;
    }
    Abc_ObjForEachFanin(pNode, pFanin, j) {
      // Find which PI this fanin corresponds to
      Abc_Obj_t* pPiTemp;
      int piIdx;
      Abc_NtkForEachPi(pNtk, pPiTemp, piIdx) {
        if (pPiTemp == pFanin) {
          piToFanin[piIdx] = j;
          break;
        }
      }
    }

    // Find Pattern 1: cofactoring produces xi
    // This happens where bCof1 = 1 and bCof0 = 0
    DdNode* bDiff1 = Cudd_bddAnd(dd, bCof1, Cudd_Not(bCof0));
    Cudd_Ref(bDiff1);

    if (Cudd_bddPickOneCube(dd, bDiff1, pCube)) {
      // Print the pattern in PI order with '-' for xi
      for (j = 0; j < nPis; j++) {
        if (j == i) {
          Abc_Print(1, "-");
        } else if (piToFanin[j] == -1) {
          // This PI is not in the support, use 0
          Abc_Print(1, "0");
        } else {
          int fidx = piToFanin[j];
          Abc_Print(1, "%c", (pCube[fidx] == 0) ? '0' : (pCube[fidx] == 1) ? '1' : '0');
        }
      }
      Abc_Print(1, "\n");
    }
    Cudd_RecursiveDeref(dd, bDiff1);

    // Find Pattern 2: cofactoring produces NOT xi
    // This happens where bCof0 = 1 and bCof1 = 0
    DdNode* bDiff2 = Cudd_bddAnd(dd, bCof0, Cudd_Not(bCof1));
    Cudd_Ref(bDiff2);

    if (Cudd_bddPickOneCube(dd, bDiff2, pCube)) {
      // Print the pattern in PI order with '-' for xi
      for (j = 0; j < nPis; j++) {
        if (j == i) {
          Abc_Print(1, "-");
        } else if (piToFanin[j] == -1) {
          // This PI is not in the support, use 0
          Abc_Print(1, "0");
        } else {
          int fidx = piToFanin[j];
          Abc_Print(1, "%c", (pCube[fidx] == 0) ? '0' : (pCube[fidx] == 1) ? '1' : '0');
        }
      }
      Abc_Print(1, "\n");
    }
    Cudd_RecursiveDeref(dd, bDiff2);

    ABC_FREE(piToFanin);
    ABC_FREE(pCube);
  }

  // Clean up
  Cudd_RecursiveDeref(dd, bCof0);
  Cudd_RecursiveDeref(dd, bCof1);
  Cudd_RecursiveDeref(dd, bFunc);
}
#else
void Lsv_NtkPrintUnateBDD(Abc_Ntk_t* pNtk, int k, int i) {
  Abc_Print(-1, "Error: CUDD is not enabled. Please compile ABC with CUDD support.\n");
}
#endif

/**Function*************************************************************

  Synopsis    [Checks the unateness of output k with respect to input i using SAT.]

  Description [For a strashed AIG network, checks whether the function of
  primary output k is positive unate, negative unate, independent of, or
  binate in primary input i. If binate, prints two patterns demonstrating
  the binateness.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Lsv_NtkPrintUnateSAT(Abc_Ntk_t* pNtk, int k, int i) {
  // Validate network type
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Error: Network is not a strashed AIG. Please run \"strash\" first.\n");
    return;
  }

  // Validate output index
  if (k < 0 || k >= Abc_NtkPoNum(pNtk)) {
    Abc_Print(-1, "Error: Output index %d is out of range [0, %d).\n", k, Abc_NtkPoNum(pNtk));
    return;
  }

  // Validate input index
  if (i < 0 || i >= Abc_NtkPiNum(pNtk)) {
    Abc_Print(-1, "Error: Input index %d is out of range [0, %d).\n", i, Abc_NtkPiNum(pNtk));
    return;
  }

  int nPis = Abc_NtkPiNum(pNtk);

  // Step 1: Convert the whole network to AIG (Dar)
  Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
  if (pAig == NULL) {
    Abc_Print(-1, "Error: Failed to convert to AIG.\n");
    return;
  }

  // Step 2: Derive CNF for all outputs
  int nCoNum = Aig_ManCoNum(pAig);
  Cnf_Dat_t* pCnfA = Cnf_Derive(pAig, nCoNum);
  if (pCnfA == NULL) {
    Abc_Print(-1, "Error: Failed to derive CNF.\n");
    Aig_ManStop(pAig);
    return;
  }

  // Get input CNF variables for copy A
  int nPisAig = Aig_ManCiNum(pAig);
  int* pVarPiA = ABC_ALLOC(int, nPisAig);
  for (int j = 0; j < nPisAig; j++) {
    Aig_Obj_t* pPiAig = Aig_ManCi(pAig, j);
    pVarPiA[j] = pCnfA->pVarNums[Aig_ObjId(pPiAig)];
  }

  // Get output CNF variable for output k
  Aig_Obj_t* pOutput = Aig_ManCo(pAig, k);
  int varOutA = pCnfA->pVarNums[Aig_ObjId(pOutput)];

  // Step 3: Create copy B variables (lifted by nVars)
  int nVarsA = pCnfA->nVars;
  int* pVarPiB = ABC_ALLOC(int, nPisAig);
  for (int j = 0; j < nPisAig; j++) {
    pVarPiB[j] = pVarPiA[j] + nVarsA;
  }
  int varOutB = varOutA + nVarsA;

  // Step 4: Create SAT solver and add CNFs
  sat_solver* pSat = sat_solver_new();
  sat_solver_setnvars(pSat, nVarsA * 2);

  // Add CNF A clauses (copy A)
  for (int c = 0; c < pCnfA->nClauses; c++) {
    if (!sat_solver_addclause(pSat, pCnfA->pClauses[c], pCnfA->pClauses[c+1])) {
      goto cleanup;
    }
  }

  // Add CNF B clauses (copy B with lifted variables)
  for (int c = 0; c < pCnfA->nClauses; c++) {
    int* pBeg = pCnfA->pClauses[c];
    int* pEnd = pCnfA->pClauses[c+1];
    int nLits = pEnd - pBeg;
    lit* pLits = ABC_ALLOC(lit, nLits);
    for (int l = 0; l < nLits; l++) {
      int var = Abc_Lit2Var(pBeg[l]);
      int isCompl = Abc_LitIsCompl(pBeg[l]);
      pLits[l] = toLitCond(var + nVarsA, isCompl);
    }
    if (!sat_solver_addclause(pSat, pLits, pLits + nLits)) {
      ABC_FREE(pLits);
      goto cleanup;
    }
    ABC_FREE(pLits);
  }

  // Step 5: Add constraints to equate all inputs except xi between copies A and B
  for (int j = 0; j < nPisAig; j++) {
    if (j != i) {
      sat_solver_add_buffer(pSat, pVarPiA[j], pVarPiB[j], 0);
    }
  }

  // Step 6 & 7: Check unateness using SAT queries
  {
    lit assumptions[4];
    
    // Check for NOT positive unate:
    // Query: f(xi=0) = 1 and f(xi=1) = 0
    // Copy A: xi = 0, output = 1
    // Copy B: xi = 1, output = 0
    assumptions[0] = toLitCond(pVarPiA[i], 1);    // xi_A = 0
    assumptions[1] = toLitCond(varOutA, 0);        // out_A = 1
    assumptions[2] = toLitCond(pVarPiB[i], 0);    // xi_B = 1
    assumptions[3] = toLitCond(varOutB, 1);        // out_B = 0

    int statusNotPos = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
    int isNotPosUnate = (statusNotPos == l_True);

    // Check for NOT negative unate:
    // Query: f(xi=1) = 1 and f(xi=0) = 0
    // Copy A: xi = 1, output = 1
    // Copy B: xi = 0, output = 0
    assumptions[0] = toLitCond(pVarPiA[i], 0);    // xi_A = 1
    assumptions[1] = toLitCond(varOutA, 0);        // out_A = 1
    assumptions[2] = toLitCond(pVarPiB[i], 1);    // xi_B = 0
    assumptions[3] = toLitCond(varOutB, 1);        // out_B = 0

    int statusNotNeg = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
    int isNotNegUnate = (statusNotNeg == l_True);

    // Determine and print result
    if (!isNotPosUnate && !isNotNegUnate) {
      Abc_Print(1, "independent\n");
    } else if (isNotPosUnate && !isNotNegUnate) {
      Abc_Print(1, "negative unate\n");
    } else if (!isNotPosUnate && isNotNegUnate) {
      Abc_Print(1, "positive unate\n");
    } else {
      // Binate - get patterns
      Abc_Print(1, "binate\n");

      // Pattern 1: from NOT negative unate query (where xi increasing causes output to increase)
      assumptions[0] = toLitCond(pVarPiA[i], 0);    // xi_A = 1
      assumptions[1] = toLitCond(varOutA, 0);        // out_A = 1
      assumptions[2] = toLitCond(pVarPiB[i], 1);    // xi_B = 0
      assumptions[3] = toLitCond(varOutB, 1);        // out_B = 0
      sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);

      // Print Pattern 1 (in original PI order)
      for (int j = 0; j < nPis; j++) {
        if (j == i) {
          Abc_Print(1, "-");
        } else if (j < nPisAig) {
          int val = sat_solver_var_value(pSat, pVarPiA[j]);
          Abc_Print(1, "%d", val);
        } else {
          Abc_Print(1, "0");
        }
      }
      Abc_Print(1, "\n");

      // Pattern 2: from NOT positive unate query (where xi increasing causes output to decrease)
      assumptions[0] = toLitCond(pVarPiA[i], 1);    // xi_A = 0
      assumptions[1] = toLitCond(varOutA, 0);        // out_A = 1
      assumptions[2] = toLitCond(pVarPiB[i], 0);    // xi_B = 1
      assumptions[3] = toLitCond(varOutB, 1);        // out_B = 0
      sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);

      // Print Pattern 2 (in original PI order)
      for (int j = 0; j < nPis; j++) {
        if (j == i) {
          Abc_Print(1, "-");
        } else if (j < nPisAig) {
          int val = sat_solver_var_value(pSat, pVarPiA[j]);
          Abc_Print(1, "%d", val);
        } else {
          Abc_Print(1, "0");
        }
      }
      Abc_Print(1, "\n");
    }
  }

cleanup:
  ABC_FREE(pVarPiA);
  ABC_FREE(pVarPiB);
  sat_solver_delete(pSat);
  Cnf_DataFree(pCnfA);
  Aig_ManStop(pAig);
}