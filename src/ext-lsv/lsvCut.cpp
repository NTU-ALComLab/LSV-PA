#include "lsvCut.h"

#include <unordered_set>
#include <vector>
#include <cstring>
#include <cstdint>
#include <cstdio>

#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"
#endif

struct Lsv_Cut_t {
  int n;
  int leaf[6];
  bool operator==(const Lsv_Cut_t& o) const {
    if (n != o.n) return false;
    for (int i = 0; i < n; i++)
      if (leaf[i] != o.leaf[i]) return false;
    return true;
  }
};

struct Lsv_CutHash_t {
  size_t operator()(const Lsv_Cut_t& c) const {
    size_t h = (size_t)c.n;
    for (int i = 0; i < c.n; i++)
      h = h * 1315423911u + (size_t)(unsigned)c.leaf[i];
    return h;
  }
};

static int Lsv_CutUnion(const Lsv_Cut_t& a, const Lsv_Cut_t& b, int nK,
                        Lsv_Cut_t* pOut) {
  int i = 0, j = 0, n = 0;
  int tmp[12];
  while (i < a.n && j < b.n) {
    if (a.leaf[i] < b.leaf[j])
      tmp[n++] = a.leaf[i++];
    else if (a.leaf[i] > b.leaf[j])
      tmp[n++] = b.leaf[j++];
    else {
      tmp[n++] = a.leaf[i++];
      j++;
    }
    if (n > nK) return 0;
  }
  while (i < a.n) {
    tmp[n++] = a.leaf[i++];
    if (n > nK) return 0;
  }
  while (j < b.n) {
    tmp[n++] = b.leaf[j++];
    if (n > nK) return 0;
  }
  pOut->n = n;
  for (int t = 0; t < n; t++) pOut->leaf[t] = tmp[t];
  return 1;
}

static void Lsv_CutAdd(std::vector<Lsv_Cut_t>& vCuts,
                       std::unordered_set<Lsv_Cut_t, Lsv_CutHash_t>& seen,
                       const Lsv_Cut_t& cut) {
  if (seen.insert(cut).second) vCuts.push_back(cut);
}

static int Lsv_EvalNode(Abc_Obj_t* pObj, const Lsv_Cut_t& cut, int assign,
                        int* pMemo) {
  int id = (int)Abc_ObjId(pObj);
  for (int i = 0; i < cut.n; i++) {
    if (cut.leaf[i] == id) return (assign >> (cut.n - 1 - i)) & 1;
  }
  if (pMemo[id] >= 0) return pMemo[id];
  if (Abc_AigNodeIsConst(pObj)) {
    pMemo[id] = 1;
    return 1;
  }
  int v0 = Lsv_EvalNode(Abc_ObjFanin0(pObj), cut, assign, pMemo) ^
           Abc_ObjFaninC0(pObj);
  int v1 = Lsv_EvalNode(Abc_ObjFanin1(pObj), cut, assign, pMemo) ^
           Abc_ObjFaninC1(pObj);
  pMemo[id] = v0 & v1;
  return pMemo[id];
}

static uint64_t Lsv_CutTruth(Abc_Obj_t* pRoot, const Lsv_Cut_t& cut,
                             std::vector<int>& memo) {
  uint64_t tt = 0;
  int nAssign = 1 << cut.n;
  int nObj = (int)memo.size();
  for (int i = 0; i < nAssign; i++) {
    for (int j = 0; j < nObj; j++) memo[j] = -1;
    if (Lsv_EvalNode(pRoot, cut, i, memo.data()))
      tt |= ((uint64_t)1) << i;
  }
  return tt;
}

static void Lsv_EnumerateCuts(Abc_Ntk_t* pNtk, int nK,
                              std::vector<std::vector<Lsv_Cut_t> >& vNodeCuts) {
  int nObjs = Abc_NtkObjNumMax(pNtk);
  vNodeCuts.assign(nObjs, std::vector<Lsv_Cut_t>());
  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachCi(pNtk, pObj, i) {
    Lsv_Cut_t c;
    c.n = 1;
    c.leaf[0] = (int)Abc_ObjId(pObj);
    vNodeCuts[Abc_ObjId(pObj)].push_back(c);
  }
  {
    Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
    Lsv_Cut_t c;
    c.n = 0;
    vNodeCuts[Abc_ObjId(pConst)].push_back(c);
  }

  // Print/store order is insertion order, not sorted by leaf IDs:
  // trivial cut first, then fanin0-cuts × fanin1-cuts in list order.
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = (int)Abc_ObjId(pObj);
    std::unordered_set<Lsv_Cut_t, Lsv_CutHash_t> seen;
    Lsv_Cut_t triv;
    triv.n = 1;
    triv.leaf[0] = id;
    Lsv_CutAdd(vNodeCuts[id], seen, triv);

    const std::vector<Lsv_Cut_t>& v0 = vNodeCuts[Abc_ObjFaninId0(pObj)];
    const std::vector<Lsv_Cut_t>& v1 = vNodeCuts[Abc_ObjFaninId1(pObj)];
    for (size_t a = 0; a < v0.size(); a++) {
      for (size_t b = 0; b < v1.size(); b++) {
        Lsv_Cut_t u;
        if (!Lsv_CutUnion(v0[a], v1[b], nK, &u)) continue;
        Lsv_CutAdd(vNodeCuts[id], seen, u);
      }
    }
  }
}

void Lsv_NtkCutTt(Abc_Ntk_t* pNtk, int nK) {
  std::vector<std::vector<Lsv_Cut_t> > vNodeCuts;
  Lsv_EnumerateCuts(pNtk, nK, vNodeCuts);
  std::vector<int> memo(Abc_NtkObjNumMax(pNtk), -1);
  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = (int)Abc_ObjId(pObj);
    const std::vector<Lsv_Cut_t>& cuts = vNodeCuts[id];
    for (size_t c = 0; c < cuts.size(); c++) {
      uint64_t tt = Lsv_CutTruth(pObj, cuts[c], memo);
      printf("%d:", id);
      for (int t = 0; t < cuts[c].n; t++) printf(" %d", cuts[c].leaf[t]);
      printf(": %lX\n", (unsigned long)tt);
    }
  }
}

#ifdef ABC_USE_CUDD
static DdNode* Lsv_BddFlip(DdNode* p) {
  return (DdNode*)((uintptr_t)p ^ (uintptr_t)1);
}

static DdNode* Lsv_BddBuild(Abc_Obj_t* pObj, const Lsv_Cut_t& cut, DdManager* dd,
                            std::vector<DdNode*>& memo, std::vector<int>& used) {
  int id = (int)Abc_ObjId(pObj);
  for (int i = 0; i < cut.n; i++) {
    if (cut.leaf[i] == id) {
      DdNode* pVar = Cudd_bddIthVar(dd, i);
      Cudd_Ref(pVar);
      return pVar;
    }
  }
  if (memo[id]) {
    Cudd_Ref(memo[id]);
    return memo[id];
  }
  if (Abc_AigNodeIsConst(pObj)) {
    DdNode* pOne = Cudd_ReadOne(dd);
    Cudd_Ref(pOne);
    memo[id] = pOne;
    Cudd_Ref(pOne);
    used.push_back(id);
    return pOne;
  }
  DdNode* p0 = Lsv_BddBuild(Abc_ObjFanin0(pObj), cut, dd, memo, used);
  DdNode* p1 = Lsv_BddBuild(Abc_ObjFanin1(pObj), cut, dd, memo, used);
  DdNode* q0 = Abc_ObjFaninC0(pObj) ? Lsv_BddFlip(p0) : p0;
  DdNode* q1 = Abc_ObjFaninC1(pObj) ? Lsv_BddFlip(p1) : p1;
  DdNode* pAnd = Cudd_bddAnd(dd, q0, q1);
  Cudd_Ref(pAnd);
  Cudd_RecursiveDeref(dd, p0);
  Cudd_RecursiveDeref(dd, p1);
  memo[id] = pAnd;
  Cudd_Ref(pAnd);
  used.push_back(id);
  return pAnd;
}

void Lsv_NtkCutBddSize(Abc_Ntk_t* pNtk, int nK) {
  std::vector<std::vector<Lsv_Cut_t> > vNodeCuts;
  Lsv_EnumerateCuts(pNtk, nK, vNodeCuts);
  DdManager* dd = Cudd_Init(nK, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Cudd_AutodynDisable(dd);
  int nObjs = Abc_NtkObjNumMax(pNtk);
  std::vector<DdNode*> memo(nObjs, (DdNode*)NULL);
  std::vector<int> used;
  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = (int)Abc_ObjId(pObj);
    const std::vector<Lsv_Cut_t>& cuts = vNodeCuts[id];
    for (size_t c = 0; c < cuts.size(); c++) {
      used.clear();
      DdNode* pBdd = Lsv_BddBuild(pObj, cuts[c], dd, memo, used);
      int nSize = Cudd_DagSize(pBdd);
      printf("%d:", id);
      for (int t = 0; t < cuts[c].n; t++) printf(" %d", cuts[c].leaf[t]);
      printf(": %d\n", nSize);
      Cudd_RecursiveDeref(dd, pBdd);
      for (size_t u = 0; u < used.size(); u++) {
        int mid = used[u];
        Cudd_RecursiveDeref(dd, memo[mid]);
        memo[mid] = NULL;
      }
    }
  }
  Cudd_Quit(dd);
}
#else
void Lsv_NtkCutBddSize(Abc_Ntk_t* pNtk, int nK) {
  (void)pNtk;
  (void)nK;
  Abc_Print(-1, "CUDD is not enabled in this ABC build.\n");
}
#endif
