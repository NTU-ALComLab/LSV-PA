#include "lsvCut.h"

#include <algorithm>
#include <iterator>
#include <set>

// Recursing through fanins also works when object IDs are not topological.
const Lsv_Cuts& Lsv_EnumerateCuts(Abc_Obj_t* pObj, int k,
                                 std::vector<Lsv_Cuts>& cuts,
                                 std::vector<bool>& done) {
  int id = Abc_ObjId(pObj);
  if (done[id]) return cuts[id];
  done[id] = true;
  if (Abc_AigNodeIsConst(pObj)) {
    cuts[id].push_back(Lsv_Cut()); // Constant one needs no input.
    return cuts[id];
  }
  cuts[id].push_back(Lsv_Cut(1, id));
  if (Abc_ObjIsCi(pObj)) return cuts[id];
  const Lsv_Cuts& left = Lsv_EnumerateCuts(Abc_ObjFanin0(pObj), k, cuts, done);
  const Lsv_Cuts& right = Lsv_EnumerateCuts(Abc_ObjFanin1(pObj), k, cuts, done);
  std::set<Lsv_Cut> seen;
  for (const Lsv_Cut& a : left) {
    for (const Lsv_Cut& b : right) {
      Lsv_Cut merged;
      std::set_union(a.begin(), a.end(), b.begin(), b.end(),
                     std::back_inserter(merged));
      if (merged.size() <= k && seen.insert(merged).second)
        cuts[id].push_back(merged);
    }
  }
  // Do not discard dominated cuts: the command requests all cuts.
  return cuts[id];
}
