#include "lsvCut.h"

#include <map>

uint64_t Lsv_TruthMask(unsigned n) {
  const unsigned bits = 1u << n;
  return bits == 64 ? UINT64_MAX : (UINT64_C(1) << bits) - 1;
}

static uint64_t Lsv_EvaluateCone(Abc_Obj_t* pObj, uint64_t mask,
                                 std::map<int, uint64_t>& values) {
  const int id = Abc_ObjId(pObj);
  const auto found = values.find(id);
  if (found != values.end()) return found->second;
  if (Abc_AigNodeIsConst(pObj)) return mask;
  // Every CI path must have been intercepted by a leaf of this cut.
  assert(!Abc_ObjIsCi(pObj));
  uint64_t a = Lsv_EvaluateCone(Abc_ObjFanin0(pObj), mask, values);
  uint64_t b = Lsv_EvaluateCone(Abc_ObjFanin1(pObj), mask, values);
  if (Abc_ObjFaninC0(pObj)) a ^= mask;
  if (Abc_ObjFaninC1(pObj)) b ^= mask;
  return values[id] = a & b;
}

uint64_t Lsv_CutTruth(Abc_Obj_t* pObj, const Lsv_Cut& cut) {
  std::map<int, uint64_t> values;
  const unsigned n = cut.size();
  for (unsigned v = 0; v < n; ++v) {
    uint64_t column = 0;
    for (unsigned assignment = 0; assignment < (1u << n); ++assignment)
      if ((assignment >> (n - 1 - v)) & 1u)
        column |= UINT64_C(1) << assignment;
    values[cut[v]] = column;
  }
  // Evaluate with all cut leaves as boundaries, including redundant leaves
  // in reconvergent cuts. No built-in cut/truth-table routines are used.
  return Lsv_EvaluateCone(pObj, Lsv_TruthMask(n), values);
}

int Lsv_NtkCutTt(Abc_Ntk_t* pNtk, int k) {
  std::vector<Lsv_Cuts> cuts(Abc_NtkObjNumMax(pNtk));
  std::vector<bool> done(cuts.size(), false);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const Lsv_Cut& cut : Lsv_EnumerateCuts(pObj, k, cuts, done)) {
      uint64_t truth = Lsv_CutTruth(pObj, cut);
      printf("%d:", Abc_ObjId(pObj));
      for (int leaf : cut) printf(" %d", leaf);
      printf(": %llX\n", (unsigned long long)truth);
    }
  }
  return 0;
}
