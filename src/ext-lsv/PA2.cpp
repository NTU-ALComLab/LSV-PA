#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <unordered_map>
#include <string>

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
  std::unordered_map<std::string, int> m_name2idx;
  DdManager * dd = (DdManager *)pNtk->pManFunc;
  
  Abc_Obj_t* pPi;
  int idx;

  // Iterate through PIs in order
  Abc_NtkForEachPi(pNtk, pPi, idx) {
      // printf("PI %d: Name = %s, Id = %d\n", idx, Abc_ObjName(pPi), Abc_ObjId(pPi));
      m_name2idx[Abc_ObjName(pPi)] = idx;
  }

  Abc_Obj_t* pPo;
  
  // Iterate through POs in order
  Abc_NtkForEachPo(pNtk, pPo, idx) {
      // printf("PO %d: Name = %s, Id = %d\n", idx, Abc_ObjName(pPo), Abc_ObjId(pPo));
  }

  // DdManager * dd = (DdManager *)pNtk->pManFunc;
  pPo = Abc_NtkPo(pNtk, k);
  pPo = Abc_ObjFanin0(pPo);
  DdNode * ddPo = (DdNode *)pPo->pData;
  
  // match the layer of the input i in the BDD by its name
  int layerOfIdiInBdd = -1;
  Vec_Ptr_t * bdd_varsname_arr = Abc_NodeGetFaninNames(pPo);
  void * pName;
  Vec_PtrForEachEntry(char *, bdd_varsname_arr, pName, idx) {
    // printf("BDD var name at layer %d: %s\n", idx, (char*)pName);
    if(strcmp((char*)pName, Abc_ObjName(Abc_NtkPi(pNtk, i))) == 0) {
      layerOfIdiInBdd = idx;
      // break;
    }
  }

  if(layerOfIdiInBdd == -1) {
    printf("independent\n");
    return;
  }

  DdNode * ddPi = Cudd_bddIthVar(dd, layerOfIdiInBdd);
  DdNode * Cof0 = Cudd_Cofactor(dd, ddPo, Cudd_Not(ddPi));
  Cudd_Ref(Cof0);
  DdNode * Cof1 = Cudd_Cofactor(dd, ddPo, ddPi);
  Cudd_Ref(Cof1);
  
  bool posUnate = Cudd_bddLeq(dd, Cof0, Cof1);
  bool negUnate = Cudd_bddLeq(dd, Cof1, Cof0);
  
  if (posUnate) {
      printf("positive unate\n");
      Cudd_RecursiveDeref(dd, Cof0);
      Cudd_RecursiveDeref(dd, Cof1);
      return;
  } else if (negUnate) {
      printf("negative unate\n");
      Cudd_RecursiveDeref(dd, Cof0);
      Cudd_RecursiveDeref(dd, Cof1);
      return;
  } else {
      printf("binate\n");
  }
  
  DdNode * nCof0 = Cudd_Not(Cof0);
  DdNode * nCof1 = Cudd_Not(Cof1);
  DdNode * ddPattern0 = Cudd_bddAnd(dd, Cof0, nCof1);
  DdNode * ddPattern1 = Cudd_bddAnd(dd, Cof1, nCof0);

  DdGen * cex1, * cex0;
  int * cube;
  CUDD_VALUE_TYPE value;
  
  // int numofpi = Abc_NtkPiNum(pNtk);
  cex1 = Cudd_FirstCube(dd, ddPattern1, &cube, &value);
  char * pattern1 = (char*)ABC_ALLOC(char, Abc_NtkPiNum(pNtk) + 1);
  memset(pattern1, '-', Abc_NtkPiNum(pNtk));
  pattern1[Abc_NtkPiNum(pNtk)] = '\0';
  Vec_PtrForEachEntry(char *, bdd_varsname_arr, pName, idx) {
    int tmp = m_name2idx[(char*)pName];
    pattern1[tmp] = cube[idx] == 0 ? '0' : cube[idx] == 1 ? '1' : '-';
  }
  printf("%s\n", pattern1);
    Cudd_GenFree(cex1);

    cex0 = Cudd_FirstCube(dd, ddPattern0, &cube, &value);
    char * pattern0 = (char*)ABC_ALLOC(char, Abc_NtkPiNum(pNtk) + 1);
    memset(pattern0, '-', Abc_NtkPiNum(pNtk));
    pattern0[Abc_NtkPiNum(pNtk)] = '\0';
    Vec_PtrForEachEntry(char *, bdd_varsname_arr, pName, idx) {
      int tmp = m_name2idx[(char*)pName];
      pattern0[tmp] = cube[idx] == 0 ? '0' : cube[idx] == 1 ? '1' : '-';
    }
    printf("%s\n", pattern0);
    Cudd_GenFree(cex0);
    ABC_FREE(pattern1);
    ABC_FREE(pattern0);
}
