#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "opt/cut/cut.h"

/*===lsv_ext ===============================================================*/
extern ABC_DLL void               Lsv_NtkPrintMOCuts( Abc_Ntk_t * pNtk ,int k, int l);

//lsv commands ==============================================================
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Abc_CommandLsvPrintMOCut         (Abc_Frame_t * pAbc, int argc, char ** argv);

/**Function*************************************************************

  Synopsis    []

  Description [initializes the lsv package]

  SideEffects []

  SeeAlso     [Cmd_CommandAdd]

***********************************************************************/
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd( pAbc, "LSV",          "lsv_printmocut", Abc_CommandLsvPrintMOCut,   0 );
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
      
      // Print inputs
      printf("Cut %d:\n", multiOutputCutCount);
      printf("  Inputs (%d): {", Vec_IntSize(pMultiCut->vLeaves));
      for (j = 0; j < Vec_IntSize(pMultiCut->vLeaves); j++) {
        if (j > 0) printf(", ");
        int nodeId = Vec_IntEntry(pMultiCut->vLeaves, j);
        Abc_Obj_t* pNode = Abc_NtkObj(pNtk, nodeId);
        printf("%s", Abc_ObjName(pNode));
      }
      printf("}\n");
      
      // Print outputs
      printf("  Outputs (%d): {", Vec_IntSize(pMultiCut->vOutputs));
      for (j = 0; j < Vec_IntSize(pMultiCut->vOutputs); j++) {
        if (j > 0) printf(", ");
        int nodeId = Vec_IntEntry(pMultiCut->vOutputs, j);
        Abc_Obj_t* pNode = Abc_NtkObj(pNtk, nodeId);
        printf("%s", Abc_ObjName(pNode));
      }
      printf("}\n\n");
    }
  }
  
  printf("Total %d-%d multi-output cuts: %d\n", k, l, multiOutputCutCount);
  
  // Clean up
  Vec_PtrForEachEntry(MultiOutputCut*, vMultiCuts, pMultiCut, i) {
    Vec_IntFree(pMultiCut->vLeaves);
    Vec_IntFree(pMultiCut->vOutputs);
    free(pMultiCut);
  }
  Vec_PtrFree(vMultiCuts);
  Cut_ManStop(pManCut);
}