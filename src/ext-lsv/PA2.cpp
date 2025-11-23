#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

void Lsv_NtkPrintNodes_ref(Abc_Ntk_t* pNtk) {
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
      Abc_Obj_t* pFanin;
      int j;
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        printf("  Fanin-%d: Id = %d, name = %s, type = %d\n", j, Abc_ObjId(pFanin),
               Abc_ObjName(pFanin), Abc_ObjType(pFanin));
      }
      if (Abc_NtkHasSop(pNtk)) {
        printf("The SOP of this node:\n%s", (char*)pObj->pData);
      }
    }
}

void unate_bdd(Abc_Ntk_t* pNtk, int k, int i) {
  // Abc_Obj_t* pNode = Abc_NtkObj(pNtk, k);
  // Abc_Obj_t* pFanin;
  // int j;
  // printf("%d",Abc_ObjId(pNode));
  
  DdManager * dd = (DdManager *)pNtk->pManFunc;
  Abc_Obj_t* pNode = Abc_NtkPo(pNtk, k);
  pNode = Abc_ObjFanin0(pNode);
  DdNode * ddPo;
  ddPo = (DdNode *)pNode->pData;
  DdNode * var = Cudd_bddIthVar(dd, i);
  DdNode * Cof0 = Cudd_Cofactor(dd, ddPo, Cudd_Not(var));
  Cudd_Ref(Cof0);
  DdNode * Cof1 = Cudd_Cofactor(dd, ddPo, var);
  Cudd_Ref(Cof1);
  bool posUnate = Cudd_bddLeq(dd, Cof0, Cof1);
  bool negUnate = Cudd_bddLeq(dd, Cof1, Cof0);
  if (posUnate) {
    if (negUnate) {
      printf("independent\n");
    } else {
      printf("posUnate\n");
    }
  } else{
    if (negUnate) {
      printf("negUnate\n");
    } else {
      printf("binate\n");
    }
  }
  Cudd_RecursiveDeref(dd, Cof0);
  Cudd_RecursiveDeref(dd, Cof1);
  // Abc_ObjForEachFanin(pNode, pFanin, j) {
  //   printf("Fanin-%d: Id = %d, name = %s, type = %d\n", j, Abc_ObjId(pFanin),
  //          Abc_ObjName(pFanin), Abc_ObjType(pFanin));
  // }
  // printf("test unate_bdd\n");
}
