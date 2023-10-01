#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

static int Lsv_CommandSimbdd(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_bdd", Lsv_CommandSimbdd, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

///////////////////////////////////////////////////////////////////////////////////

int Lsv_NtkSimBdd(Abc_Ntk_t* pNtk, char* argv) {  
  Abc_Obj_t *pPo = 0;
  int ithPo = 0;
  Abc_NtkForEachPo(pNtk, pPo, ithPo) {
    Abc_Obj_t *pFanin = 0, *pRoot = Abc_ObjFanin0(pPo);    
    int  ithPi = 0;
    //char** vNamesIn = (char**) Abc_NodeGetFaninNames(pRoot)->pArray;
    //printf("PO_%d: %s\n", Abc_ObjId(pPo), Abc_ObjName(pPo)); //show all POs.
    assert(Abc_NtkIsBddLogic(pRoot->pNtk));
    DdManager * dd = (DdManager *)pRoot->pNtk->pManFunc;
    DdNode* ddnode = (DdNode *)pRoot->pData;
    Abc_ObjForEachFanin(pRoot, pFanin, ithPi) {      
      //printf("Fanin_%d: %s\n", ithPi, vNamesIn[ithPi]);
      DdNode* PiVar = Cudd_bddIthVar(dd, ithPi);
      if (argv[ithPi] == '1') {
        //printf("argv[%d] = %d\n", ithPi, argv[ithPi]);
        ddnode = Cudd_Cofactor(dd, ddnode, PiVar);
        
      }
      else if (argv[ithPi] == '0') {
        //printf("argv[%d] = %d\n", ithPi, argv[ithPi]);
        ddnode = Cudd_Cofactor(dd, ddnode, Cudd_Not(PiVar));
      }
      else {
        printf("Illegal inputs detected.\n");
        return 0;
      }      
    }
    printf("%s: %d\n", Abc_ObjName(pPo), ddnode==dd->one);
  }
  return 1;
}

///////////////////////////////////////////////////////////////////////////////////

int Lsv_CommandSimbdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  //printf("Input: %s\n", argv[1]);
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkSimBdd(pNtk, argv[1]);
  return 0;
}
