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
  int i, cutCount = 0;
  
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
  
  // Print k-feasible cuts for all PI and AND nodes
  printf("k-feasible Cuts (k=%d):\n", k);
  printf("========================\n");
  
  // Print cuts for Primary Inputs
  printf("Primary Inputs:\n");
  Abc_NtkForEachCi(pNtk, pObj, i) {
    if (Abc_ObjFanoutNum(pObj) > 0) {
      pList = (Cut_Cut_t*)Abc_NodeReadCuts(pManCut, pObj);
      if (pList) {
        Cut_Cut_t* pCut;
        int nodeCutCount = 0;
        
        // Count and print k-feasible cuts for this PI
        for (pCut = pList; pCut; pCut = pCut->pNext) {
          if (pCut->nLeaves <= k) { // k-feasible cut
            nodeCutCount++;
          }
        }
        
        if (nodeCutCount > 0) {
          printf("Node %s (ID=%d): %d cuts\n", Abc_ObjName(pObj), Abc_ObjId(pObj), nodeCutCount);
          
          // Print individual cuts
          for (pCut = pList; pCut; pCut = pCut->pNext) {
            if (pCut->nLeaves <= k) { // k-feasible cut
              printf("  ");
              Cut_CutPrint(pCut, 0);
              printf("\n");
              cutCount++;
            }
          }
          printf("\n");
        }
      }
    }
  }
  
  // Print cuts for AND nodes
  printf("AND Nodes:\n");
  Abc_NtkForEachNode(pNtk, pObj, i) {
    pList = (Cut_Cut_t*)Abc_NodeReadCuts(pManCut, pObj);
    if (pList) {
      Cut_Cut_t* pCut;
      int nodeCutCount = 0;
      
      // Count k-feasible cuts for this AND node
      for (pCut = pList; pCut; pCut = pCut->pNext) {
        if (pCut->nLeaves <= k) { // k-feasible cut
          nodeCutCount++;
        }
      }
      
      if (nodeCutCount > 0) {
        printf("Node %s (ID=%d): %d cuts\n", Abc_ObjName(pObj), Abc_ObjId(pObj), nodeCutCount);
        
        // Print individual cuts
        for (pCut = pList; pCut; pCut = pCut->pNext) {
          if (pCut->nLeaves <= k) { // k-feasible cut
            printf("  ");
            Cut_CutPrint(pCut, 0);
            printf("\n");
            cutCount++;
          }
        }
        printf("\n");
      }
    }
  }
  
  printf("Total irredundant k-feasible cuts found: %d\n", cutCount);
  
  // Clean up
  Cut_ManStop(pManCut);
}