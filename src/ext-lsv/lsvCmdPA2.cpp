#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <iostream>
#include <string.h>
using namespace std;

static int Lsv_CommandPrintpounate(Abc_Frame_t* pAbc, int argc, char** argv);

void initpounate(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintpounate, 0);
}

void destroypounate(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializerpounate = {initpounate, destroypounate};

struct PackageRegistrationManagerpounate {
  PackageRegistrationManagerpounate() { Abc_FrameAddInitializer(&frame_initializerpounate); }
} lsvPackageRegistrationManagerpounate;

// initial ok

struct inputnode{
  unsigned ID;
  char* name;
  int type;
  // 0: init didn't use
  // 1: have pos
  // 2: have negitive
  // 3: binate
};

void Lsv_NtkPrintpounate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    Abc_Obj_t* pFanin;
    int j;
    //get input
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),Abc_ObjName(pFanin)); //return char*
    }
    inputnode node[j];
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      node[j].ID = Abc_ObjId(pFanin);
      node[j].name = Abc_ObjName(pFanin);
      node[j].type = 0;
    }
    //get SOP
    char* SOP = NULL;
    if (Abc_NtkHasSop(pNtk)) {
      SOP = (char*)pObj->pData;
      cout << SOP << endl;
      //it is SOP char list
    }
  }
}

int Lsv_CommandPrintpounate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintpounate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_pounateunate [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}