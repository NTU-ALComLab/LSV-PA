#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "lsvUtils.h"

static int Lsv_CommandPrintSopUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init_PrintSopUnate(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopUnate, 0);
}

void destroy_PrintSopUnate(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer_PrintSopUnate = {init_PrintSopUnate, destroy_PrintSopUnate};

struct PackageRegistrationManager_PrintSopUnate {
  PackageRegistrationManager_PrintSopUnate() { Abc_FrameAddInitializer(&frame_initializer_PrintSopUnate); }
} lsvPackageRegistrationManager_PrintSopUnate;


void Lsv_NtkPrintSopUnate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t * pObj;
  int i, j;

  Abc_NtkForEachNode(pNtk, pObj, i) {
    int nFanins = Abc_ObjFaninNum(pObj);
    if (nFanins == 0) continue;
    char * pSop = (char *)pObj->pData;
    char * pCube;
    char val;
    bool unateTable[nFanins][2] = {};
    Abc_SopForEachCube(pSop, nFanins, pCube) {
      bool isOnset = *(pCube + nFanins + 1) - '0';
      Abc_CubeForEachVar(pCube, val, j) {
        if (val == '-') continue;
        bool isOne = val - '0';
        unateTable[j][isOne == isOnset] = 1;
      }
    }
    
    Vec_Ptr_t * posUnateVec = Vec_PtrAlloc( nFanins );
    Vec_Ptr_t * negUnateVec = Vec_PtrAlloc( nFanins );
    Vec_Ptr_t * binateVec = Vec_PtrAlloc( nFanins );
    Abc_Obj_t * pFanin;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      if (unateTable[j][0] && unateTable[j][1]) 
        Vec_PtrPush( binateVec, pFanin );
      else {
        if (!unateTable[j][0]) Vec_PtrPush( posUnateVec, pFanin );
        if (!unateTable[j][1]) Vec_PtrPush( negUnateVec, pFanin );
      }
    }

    Vec_PtrSort( posUnateVec, (int (*)()) Lsv_sortCompare );
    Vec_PtrSort( negUnateVec, (int (*)()) Lsv_sortCompare );
    Vec_PtrSort( binateVec, (int (*)()) Lsv_sortCompare );

    printf("node %s:\n", Abc_ObjName(pObj));
    Lsv_printInputs( "+unate inputs", posUnateVec );
    Lsv_printInputs( "-unate inputs", negUnateVec );
    Lsv_printInputs( "binate inputs", binateVec );

    Vec_PtrFree( posUnateVec );
    Vec_PtrFree( negUnateVec );
    Vec_PtrFree( binateVec );
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
