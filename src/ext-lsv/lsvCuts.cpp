#include "lsvCuts.h"

#include <algorithm>
#include <iterator>

static void Lsv_AddUniqueCut(
    Lsv_CutList& cuts,
    Lsv_Cut cut) {
  std::sort(cut.begin(), cut.end());

  for (const Lsv_Cut& oldCut : cuts) {
    if (oldCut == cut) {
      return;
    }
  }

  cuts.push_back(cut);
}

static Lsv_Cut Lsv_MergeCuts(
    const Lsv_Cut& a,
    const Lsv_Cut& b) {
  Lsv_Cut result;

  std::set_union(
      a.begin(),
      a.end(),
      b.begin(),
      b.end(),
      std::back_inserter(result));

  return result;
}

const Lsv_CutList& Lsv_ComputeCuts(
    Abc_Obj_t* pObj,
    int k,
    Lsv_AllCuts& allCuts,
    std::vector<char>& computed) {
  Abc_Obj_t* pRegular = Abc_ObjRegular(pObj);
  int id = Abc_ObjId(pRegular);

  if (computed[id]) {
    return allCuts[id];
  }

  computed[id] = 1;

  Lsv_CutList& cuts = allCuts[id];

  // ABC's constant-one object
  if (pRegular->Type == ABC_OBJ_CONST1) {
    cuts.push_back(Lsv_Cut());
    return cuts;
  }

  // Primary input
  if (Abc_ObjIsPi(pRegular)) {
    cuts.push_back(Lsv_Cut(1, id));
    return cuts;
  }

  // Trivial cut containing only the current node
  cuts.push_back(Lsv_Cut(1, id));

  if (!Abc_ObjIsNode(pRegular) ||
      Abc_ObjFaninNum(pRegular) != 2) {
    return cuts;
  }

  Abc_Obj_t* pFanin0 =
      Abc_ObjFanin(pRegular, 0);

  Abc_Obj_t* pFanin1 =
      Abc_ObjFanin(pRegular, 1);

  const Lsv_CutList& cuts0 =
      Lsv_ComputeCuts(
          pFanin0,
          k,
          allCuts,
          computed);

  const Lsv_CutList& cuts1 =
      Lsv_ComputeCuts(
          pFanin1,
          k,
          allCuts,
          computed);

  for (const Lsv_Cut& cut0 : cuts0) {
    for (const Lsv_Cut& cut1 : cuts1) {
      Lsv_Cut merged =
          Lsv_MergeCuts(cut0, cut1);

      // The root must not appear in a nontrivial merged cut
      if (std::binary_search(
              merged.begin(),
              merged.end(),
              id)) {
        continue;
      }

      if (static_cast<int>(merged.size()) <= k) {
        Lsv_AddUniqueCut(cuts, merged);
      }
    }
  }

  std::sort(
      cuts.begin(),
      cuts.end(),
      [](const Lsv_Cut& a, const Lsv_Cut& b) {
        if (a.size() != b.size()) {
          return a.size() < b.size();
        }

        return a < b;
      });

  return cuts;
}
