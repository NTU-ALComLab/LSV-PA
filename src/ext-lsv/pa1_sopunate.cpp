#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

/*========== DECLARE ==========*/

static int Lsv_CommandPrintSopUnate(Abc_Frame_t* pAbc, int argc, char** argv);
static void printNodeUnateInfo(Abc_Obj_t*, Vec_Ptr_t*, Vec_Ptr_t*, Vec_Ptr_t*);
static void printObjNameInVec(Vec_Ptr_t*);
static int Vec_PtrSortCompareObjId(void** pp1, void** pp2) {
  Abc_Obj_t* pObj1 = (Abc_Obj_t*)*pp1;
  Abc_Obj_t* pObj2 = (Abc_Obj_t*)*pp2;
  if (Abc_ObjId(pObj1) < Abc_ObjId(pObj2)) return -1;
  if (Abc_ObjId(pObj1) > Abc_ObjId(pObj2)) return 1;
  return 0;
}

/*========== ABC STARTUP AND TERMINATION ==========*/

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

/*==========  LSV PA1 SOPUNATE ==========*/
 /*===== Each of node is combined with many fanin. We search all cubes of this fanin,
  for one fanin there has three state:
  (1)Binate:if there both exists positve lit and negative lit=====
  (2)PosUnate:just exists positive lit
  (3)NegUnate:just exits negative lit
 ======*/

void Lsv_NtkPrintSopUnate(Abc_Ntk_t* pNtk) {
  Vec_Ptr_t* vPosUnate = Vec_PtrAlloc(8);//The number of eight is just a prememory allocate
  Vec_Ptr_t* vNegUnate = Vec_PtrAlloc(8);
  Vec_Ptr_t* vBinate = Vec_PtrAlloc(8);
  Abc_Obj_t* pNode;
  
  int i;//node i
  Abc_NtkForEachNode(pNtk, pNode, i){//for each node of ntk
    Vec_PtrClear(vPosUnate);//clear vector
    Vec_PtrClear(vNegUnate);
    Vec_PtrClear(vBinate);
    int j;//fanin j
    Abc_Obj_t* pFanin;
    char* pSop = (char*)pNode -> pData;//get the pData of the pNode. (char*)?
    Abc_ObjForEachFanin(pNode, pFanin, j){//for each fanin of node
      char* pCube;
      bool existPosLit = false;
      bool existNegLit = false;
      Abc_SopForEachCube(pSop, Abc_SopGetVarNum(pSop), pCube) {//ex: pCube[j=0],pCube[j=1]...for one of variable
        if(!existPosLit) {
          if(pCube[j] == '1')existPosLit = true;
        }
        if(!existNegLit) {
          if(pCube[j] == '0')existNegLit = true;
        }                
      }
      if(existPosLit && existNegLit) Vec_PtrPush(vBinate, pFanin);
      if(!existNegLit) Vec_PtrPush(vPosUnate, pFanin);
      if(!existPosLit) Vec_PtrPush(vNegUnate, pFanin);
    }
    //sort the id
    Vec_PtrSort(vPosUnate, (int (*)())Vec_PtrSortCompareObjId);
    Vec_PtrSort(vNegUnate, (int (*)())Vec_PtrSortCompareObjId);
    Vec_PtrSort(vBinate, (int (*)())Vec_PtrSortCompareObjId);
    //consider the sop phase(express in oneset or offset)
    if (Abc_SopGetPhase(pSop)) {
      printNodeUnateInfo(pNode, vPosUnate, vNegUnate, vBinate);
    } 
    else {
      printNodeUnateInfo(pNode, vNegUnate, vPosUnate, vBinate);
    }
  }
  Vec_PtrFree(vPosUnate);
  Vec_PtrFree(vNegUnate);
  Vec_PtrFree(vBinate);
}

void printNodeUnateInfo(Abc_Obj_t* pNode, Vec_Ptr_t* pVecPosUnate, Vec_Ptr_t* pVecNegUnate, Vec_Ptr_t* pVecBinate) {
  if (Vec_PtrSize(pVecPosUnate) || Vec_PtrSize(pVecNegUnate) || Vec_PtrSize(pVecBinate)) {
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