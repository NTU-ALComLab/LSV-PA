#include <unordered_map>

#include "ext-lsv/pa1/lsvCut.h"

// Same descent as lsvTruth.cpp with Cudd_bddAnd for & and Cudd_Not for ~.
// Nodes are borrowed: memo holds the only reference to each result, and
// Lsv_CutBddSize releases them together at the end.
static DdNode* Lsv_BddRec(DdManager* dd, Abc_Obj_t* pObj,
                          const std::unordered_map<int, int>& leaves,
                          std::unordered_map<int, DdNode*>& memo) {
  int id = Abc_ObjId(pObj);

  std::unordered_map<int, int>::const_iterator leaf = leaves.find(id);
  if (leaf != leaves.end()) {
    return Cudd_bddIthVar(dd, leaf->second);
  }
  if (Abc_AigNodeIsConst(pObj)) {
    return Cudd_ReadOne(dd);
  }

  std::unordered_map<int, DdNode*>::iterator hit = memo.find(id);
  if (hit != memo.end()) {
    return hit->second;
  }

  DdNode* f0 = Lsv_BddRec(dd, Abc_ObjFanin0(pObj), leaves, memo);
  DdNode* f1 = Lsv_BddRec(dd, Abc_ObjFanin1(pObj), leaves, memo);
  if (Abc_ObjFaninC0(pObj)) {
    f0 = Cudd_Not(f0);
  }
  if (Abc_ObjFaninC1(pObj)) {
    f1 = Cudd_Not(f1);
  }

  DdNode* r = Cudd_bddAnd(dd, f0, f1);
  Cudd_Ref(r);
  memo[id] = r;
  return r;
}

int Lsv_CutBddSize(DdManager* dd, Abc_Obj_t* pRoot, const Lsv_Cut_t& cut) {
  std::unordered_map<int, int> leaves;
  for (size_t j = 0; j < cut.size(); ++j) {
    leaves[cut[j]] = (int)j;
  }

  std::unordered_map<int, DdNode*> memo;
  int size = Cudd_DagSize(Lsv_BddRec(dd, pRoot, leaves, memo));

  std::unordered_map<int, DdNode*>::iterator it;
  for (it = memo.begin(); it != memo.end(); ++it) {
    Cudd_RecursiveDeref(dd, it->second);
  }
  return size;
}
