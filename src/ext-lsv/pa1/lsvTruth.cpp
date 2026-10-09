#include <unordered_map>

#include "ext-lsv/pa1/lsvCut.h"

// Leaf j of an m-leaf cut sits at bit (m-1-j) of the index, so leaf 0 is the
// most significant variable.
static uint64_t Lsv_VarMask(int j, int m) {
  int pos = m - 1 - j;
  uint64_t mask = 0;
  for (int i = 0; i < (1 << m); ++i) {
    if ((i >> pos) & 1) {
      mask |= (uint64_t)1 << i;
    }
  }
  return mask;
}

static uint64_t Lsv_TruthRec(Abc_Obj_t* pObj,
                             const std::unordered_map<int, int>& leaves, int m,
                             std::unordered_map<int, uint64_t>& memo) {
  int id = Abc_ObjId(pObj);

  std::unordered_map<int, int>::const_iterator leaf = leaves.find(id);
  if (leaf != leaves.end()) {
    return Lsv_VarMask(leaf->second, m);
  }
  if (Abc_AigNodeIsConst(pObj)) {
    return ~(uint64_t)0;
  }

  std::unordered_map<int, uint64_t>::iterator hit = memo.find(id);
  if (hit != memo.end()) {
    return hit->second;
  }

  uint64_t t0 = Lsv_TruthRec(Abc_ObjFanin0(pObj), leaves, m, memo);
  uint64_t t1 = Lsv_TruthRec(Abc_ObjFanin1(pObj), leaves, m, memo);
  if (Abc_ObjFaninC0(pObj)) {
    t0 = ~t0;
  }
  if (Abc_ObjFaninC1(pObj)) {
    t1 = ~t1;
  }

  memo[id] = t0 & t1;
  return memo[id];
}

uint64_t Lsv_CutTruth(Abc_Obj_t* pRoot, const Lsv_Cut_t& cut) {
  int m = (int)cut.size();

  std::unordered_map<int, int> leaves;
  for (int j = 0; j < m; ++j) {
    leaves[cut[j]] = j;
  }

  std::unordered_map<int, uint64_t> memo;
  uint64_t t = Lsv_TruthRec(pRoot, leaves, m, memo);

  // Keep the low 2^m bits only; shifting by 64 would be undefined.
  if (m == 6) {
    return t;
  }
  return t & (((uint64_t)1 << (1 << m)) - 1);
}
