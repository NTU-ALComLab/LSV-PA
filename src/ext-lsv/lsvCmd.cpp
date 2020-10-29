#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);

static void printNodeUnateInfo(Abc_Obj_t*, Vec_Ptr_t*, Vec_Ptr_t*, Vec_Ptr_t*);
static void printObjNameInVec(Vec_Ptr_t*);
static int Vec_PtrSortCompareObjId(void** pp1, void** pp2) {
  Abc_Obj_t* pObj1 = (Abc_Obj_t*)*pp1;
  Abc_Obj_t* pObj2 = (Abc_Obj_t*)*pp2;
  if (Abc_ObjId(pObj1) < Abc_ObjId(pObj2)) return -1;
  if (Abc_ObjId(pObj1) > Abc_ObjId(pObj2)) return 1;
  return 0;
}
static int Lsv_CommandPrintSopUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_gates", Lsv_CommandPrintGates, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopUnate, 0);
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

void Lsv_NtkPrintSopUnate(Abc_Ntk_t* pNtk) {
  Vec_Ptr_t* vPosUnate = Vec_PtrAlloc(8);
  Vec_Ptr_t* vNegUnate = Vec_PtrAlloc(8);
  Vec_Ptr_t* vBinate = Vec_PtrAlloc(8);
  Abc_Obj_t* pNode;
  int i;
  Abc_NtkForEachNode(pNtk, pNode, i) {
    Vec_PtrClear(vPosUnate);
    Vec_PtrClear(vNegUnate);
    Vec_PtrClear(vBinate);
    char* pSop = (char*)pNode->pData;
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pNode, pFanin, j) {
      bool hasPosLit = false, hasNegLit = false;
      char* pCube;
      Abc_SopForEachCube(pSop, Abc_SopGetVarNum(pSop), pCube) {
        if (!hasPosLit && pCube[j] == '1') {
          hasPosLit = true;
        }
        if (!hasNegLit && pCube[j] == '0') {
          hasNegLit = true;
        }
      }
      if (!hasNegLit) {
        Vec_PtrPush(vPosUnate, pFanin);
      }
      if (!hasPosLit) {
        Vec_PtrPush(vNegUnate, pFanin);
      }
      if (hasPosLit && hasNegLit) {
        Vec_PtrPush(vBinate, pFanin);
      }
    }
    Vec_PtrSort(vPosUnate, (int (*)())Vec_PtrSortCompareObjId);
    Vec_PtrSort(vNegUnate, (int (*)())Vec_PtrSortCompareObjId);
    Vec_PtrSort(vBinate, (int (*)())Vec_PtrSortCompareObjId);
    if (Abc_SopGetPhase(pSop)) {
      printNodeUnateInfo(pNode, vPosUnate, vNegUnate, vBinate);
    } else {
      printNodeUnateInfo(pNode, vNegUnate, vPosUnate, vBinate);
    }
  }
  Vec_PtrFree(vPosUnate);
  Vec_PtrFree(vNegUnate);
  Vec_PtrFree(vBinate);
}

void printNodeUnateInfo(Abc_Obj_t* pNode, Vec_Ptr_t* pVecPosUnate, Vec_Ptr_t* pVecNegUnate, Vec_Ptr_t* pVecBinate) {
  if (Vec_PtrSize(pVecPosUnate) || Vec_PtrSize(pVecNegUnate) ||
      Vec_PtrSize(pVecBinate)) {
    printf("node %s:\n", Abc_ObjName(pNode));
    if (Vec_PtrSize(pVecPosUnate)) {
      printf("+unate inputs: ");
      printObjNameInVec(pVecPosUnate);
    }
    if (Vec_PtrSize(pVecNegUnate)) {
      printf("-unate inputs: ");
      printObjNameInVec(pVecNegUnate);
    }
    if (Vec_PtrSize(pVecBinate)) {
      printf("binate inputs: ");
      printObjNameInVec(pVecBinate);
    }
  }
}

void printObjNameInVec(Vec_Ptr_t* pVec) {
  Abc_Obj_t* pFanin;
  int j;
  Vec_PtrForEachEntry(Abc_Obj_t*, pVec, pFanin, j) {
    printf("%s", Abc_ObjName(pFanin));
    if (j < Vec_PtrSize(pVec) - 1) {
      printf(",");
    }
  }
  printf("\n");
}


int Lsv_CommandPrintSopUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintSopUnate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t   print the unate information for each node, whose function is expressed in the SOP form");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}