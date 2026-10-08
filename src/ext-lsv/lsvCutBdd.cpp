#include "lsvCut.h"

#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"

// Shannon expansion: the first (smallest-ID) variable splits the truth
// table into its low and high halves. Return one owned CUDD reference.
static DdNode* Lsv_BuildBdd(DdManager* pDd, uint64_t truth, unsigned n,
                            unsigned level = 0) {
  if (truth == 0 || truth == Lsv_TruthMask(n)) {
    DdNode* pResult = truth == 0 ? Cudd_ReadLogicZero(pDd) : Cudd_ReadOne(pDd);
    Cudd_Ref(pResult);
    return pResult;
  }
  const unsigned half = 1u << (n - 1);
  DdNode* pLow = Lsv_BuildBdd(pDd, truth & Lsv_TruthMask(n - 1), n - 1, level + 1);
  if (!pLow) return NULL;
  DdNode* pHigh = Lsv_BuildBdd(pDd, truth >> half, n - 1, level + 1);
  if (!pHigh) {
    Cudd_RecursiveDeref(pDd, pLow);
    return NULL;
  }
  DdNode* pResult = Cudd_bddIte(pDd, Cudd_bddIthVar(pDd, level), pHigh, pLow);
  if (pResult) Cudd_Ref(pResult);
  Cudd_RecursiveDeref(pDd, pLow);
  Cudd_RecursiveDeref(pDd, pHigh);
  return pResult;
}
#endif

int Lsv_NtkCutBddSize(Abc_Ntk_t* pNtk, int k) {
#ifdef ABC_USE_CUDD
  DdManager* pDd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  if (!pDd) {
    Abc_Print(-1, "Could not initialize CUDD.\n");
    return 1;
  }
  // CUDD starts with reordering disabled; variable indices follow cut IDs.
  std::vector<Lsv_Cuts> cuts(Abc_NtkObjNumMax(pNtk));
  std::vector<bool> done(cuts.size(), false);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const Lsv_Cut& cut : Lsv_EnumerateCuts(pObj, k, cuts, done)) {
      uint64_t truth = Lsv_CutTruth(pObj, cut);
      DdNode* pRoot = Lsv_BuildBdd(pDd, truth, cut.size());
      if (!pRoot) {
        Abc_Print(-1, "Could not construct cut BDD.\n");
        Cudd_Quit(pDd);
        return 1;
      }
      int size = Cudd_DagSize(pRoot);
      Cudd_RecursiveDeref(pDd, pRoot);
      printf("%d:", Abc_ObjId(pObj));
      for (int leaf : cut) printf(" %d", leaf);
      printf(": %d\n", size);
    }
  }
  Cudd_Quit(pDd);
  return 0;
#else
  Abc_Print(-1, "BDD size requires a build with CUDD enabled.\n");
  return 1;
#endif
}
