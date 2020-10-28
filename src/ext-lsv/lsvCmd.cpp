/****************************************************************************
  FileName     [ lsvCmd.cpp ]
  PackageName  [ print_sopunate ]
  Synopsis     [ Define print_sopunate commands ]
  Author       [ Qi-Yu Chen (r07943034) ]
  Copyright    [ Copyleft(c) Alcom, GIEE, NTU, Taiwan ]
 ****************************************************************************/
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

static int Lsv_CommandPrintSopUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void PrintUnateInfo(char* str, Vec_Ptr_t* vec){
  Abc_Obj_t* pEntry;
  int i;
  
  if(Vec_PtrSize(vec) == 0)
    return;
  printf("%s: ", str);
  Vec_PtrForEachEntry(Abc_Obj_t* , vec, pEntry, i){
    printf("%s", Abc_ObjName(pEntry));
    if(i == Vec_PtrSize(vec) - 1)
      printf("%c", '\n');
    else
      printf("%c", ',');
  }
}

static int Vec_PtrSortCompare(Abc_Obj_t** pp1, Abc_Obj_t** pp2){
  return Abc_ObjId(*pp1) > Abc_ObjId(*pp2);
}

void Lsv_NtkPrintSopUnate(Abc_Ntk_t* pNtk){
  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachNode(pNtk, pObj, i){
    char* pSop = (char*)pObj->pData;
    int nFanins = Abc_ObjFaninNum(pObj);
    char* pCube;
    bool unateTable[nFanins][2] = {0};
    
    Abc_SopForEachCube(pSop, nFanins, pCube){
      char Value;
      int j;
      bool isOnset = *(pCube + nFanins + 1) - '0';
      
      Abc_CubeForEachVar(pCube, Value, j){
        if(Value == '-')
          continue;
        if(Value - '0' == isOnset)
          unateTable[j][1] = 1;
        else
          unateTable[j][0] = 1;
      }
    }
    
    if(nFanins == 0)
      continue;
    Vec_Ptr_t* Vec_posUnate = Vec_PtrAlloc(nFanins);
    Vec_Ptr_t* Vec_negUnate = Vec_PtrAlloc(nFanins);
    Vec_Ptr_t* Vec_binate = Vec_PtrAlloc(nFanins);
    
    Abc_Obj_t* pFanin;
    int k;
    Abc_ObjForEachFanin(pObj, pFanin, k){
      if(!unateTable[k][0])
        Vec_PtrPush(Vec_posUnate, pFanin);
      if(!unateTable[k][1])
        Vec_PtrPush(Vec_negUnate, pFanin);
      if(unateTable[k][0] && unateTable[k][1])
        Vec_PtrPush(Vec_binate, pFanin);
    }

    Vec_PtrSort(Vec_posUnate, (int (*)()) Vec_PtrSortCompare);
    Vec_PtrSort(Vec_negUnate, (int (*)()) Vec_PtrSortCompare);
    Vec_PtrSort(Vec_binate, (int (*)()) Vec_PtrSortCompare);

    printf("node %s:\n", Abc_ObjName(pObj));
    PrintUnateInfo("+unate inputs", Vec_posUnate);
    PrintUnateInfo("-unate inputs", Vec_negUnate);
    PrintUnateInfo("binate inputs", Vec_binate);

    Vec_PtrFree(Vec_posUnate);
    Vec_PtrFree(Vec_negUnate);
    Vec_PtrFree(Vec_binate);
  }
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
  Abc_Print(-2, "\t        prints the unate information for each node\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
