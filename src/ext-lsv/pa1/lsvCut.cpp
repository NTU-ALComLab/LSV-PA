#include "ext-lsv/pa1/lsvCut.h"

int Lsv_CutUnion(const Lsv_Cut_t& a, const Lsv_Cut_t& b, int k, Lsv_Cut_t& out) {
  out.clear();
  size_t i = 0, j = 0;
  while (i < a.size() || j < b.size()) {
    // Whatever is left is larger than everything in out, so it is a new leaf.
    if ((int)out.size() == k) {
      return 0;
    }
    if (j == b.size() || (i < a.size() && a[i] < b[j])) {
      out.push_back(a[i++]);
    } else if (i == a.size() || b[j] < a[i]) {
      out.push_back(b[j++]);
    } else {
      out.push_back(a[i++]);
      ++j;
    }
  }
  return 1;
}

int Lsv_CutSetHas(const Lsv_CutSet_t& set, const Lsv_Cut_t& cut) {
  for (size_t i = 0; i < set.size(); ++i) {
    if (set[i] == cut) {
      return 1;
    }
  }
  return 0;
}

// cuts[n] = {n} U { A U B : A in cuts[fanin0], B in cuts[fanin1], |A U B| <= k }
//
// One forward pass is enough: in a strashed AIG a fanin always has a smaller
// ID, and Abc_AigForEachAnd walks the objects by increasing ID.
void Lsv_NtkEnumCuts(Abc_Ntk_t* pNtk, int k, std::vector<Lsv_CutSet_t>& cuts) {
  cuts.clear();
  cuts.resize(Abc_NtkObjNumMax(pNtk));

  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachCi(pNtk, pObj, i) {
    cuts[Abc_ObjId(pObj)].push_back(Lsv_Cut_t(1, Abc_ObjId(pObj)));
  }

  // A constant depends on nothing, so its only cut is empty.
  cuts[Abc_ObjId(Abc_AigConst1(pNtk))].push_back(Lsv_Cut_t());

  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    const Lsv_CutSet_t& s0 = cuts[Abc_ObjId(Abc_ObjFanin0(pObj))];
    const Lsv_CutSet_t& s1 = cuts[Abc_ObjId(Abc_ObjFanin1(pObj))];
    Lsv_CutSet_t& self = cuts[id];

    self.push_back(Lsv_Cut_t(1, id));

    Lsv_Cut_t c;
    for (size_t x = 0; x < s0.size(); ++x) {
      for (size_t y = 0; y < s1.size(); ++y) {
        if (Lsv_CutUnion(s0[x], s1[y], k, c) && !Lsv_CutSetHas(self, c)) {
          self.push_back(c);
        }
      }
    }
  }
}
