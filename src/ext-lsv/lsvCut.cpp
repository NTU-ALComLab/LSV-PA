#include "lsvCut.h"

#include "bdd/cudd/cuddInt.h"

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace {

using Cut = std::vector<int>;
using CutList = std::vector<Cut>;

Cut MergeCuts(const Cut& a, const Cut& b) {
  Cut result;
  result.reserve(a.size() + b.size());
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] < b[j]) {
      result.push_back(a[i++]);
    } else if (a[i] > b[j]) {
      result.push_back(b[j++]);
    } else {
      result.push_back(a[i]);
      ++i;
      ++j;
    }
  }
  while (i < a.size()) result.push_back(a[i++]);
  while (j < b.size()) result.push_back(b[j++]);
  return result;
}

// True iff a is a (possibly improper) subset of b. Both cuts must be sorted.
bool IsSubset(const Cut& a, const Cut& b) {
  if (a.size() > b.size()) {
    return false;
  }
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] == b[j]) {
      ++i;
      ++j;
    } else if (a[i] > b[j]) {
      ++j;
    } else {
      return false;
    }
  }
  return i == a.size();
}

// Drop cuts that are proper supersets of another cut of the same node
// (TA clarification on dominated cuts; see LSV-PA#983).
void FilterDominatedCuts(CutList& cuts) {
  CutList kept;
  kept.reserve(cuts.size());
  for (size_t i = 0; i < cuts.size(); ++i) {
    bool dominated = false;
    for (size_t j = 0; j < cuts.size(); ++j) {
      if (i == j) {
        continue;
      }
      if (cuts[j].size() < cuts[i].size() && IsSubset(cuts[j], cuts[i])) {
        dominated = true;
        break;
      }
    }
    if (!dominated) {
      kept.push_back(cuts[i]);
    }
  }
  cuts.swap(kept);
}

void CollectCone(Abc_Obj_t* pObj, const std::unordered_set<int>& leafSet,
                 std::unordered_set<int>& visited, std::vector<Abc_Obj_t*>& cone) {
  int id = Abc_ObjId(pObj);
  if (leafSet.count(id) || visited.count(id) || Abc_AigNodeIsConst(pObj)) {
    return;
  }
  visited.insert(id);
  if (!Abc_AigNodeIsAnd(pObj)) {
    return;
  }
  CollectCone(Abc_ObjFanin0(pObj), leafSet, visited, cone);
  CollectCone(Abc_ObjFanin1(pObj), leafSet, visited, cone);
  cone.push_back(pObj);
}

std::vector<CutList> EnumerateCuts(Abc_Ntk_t* pNtk, int k) {
  int nObjs = Abc_NtkObjNumMax(pNtk);
  std::vector<CutList> cuts(nObjs);

  Abc_Obj_t* pConst1 = Abc_AigConst1(pNtk);
  cuts[Abc_ObjId(pConst1)].push_back(Cut());

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachCi(pNtk, pObj, i) {
    Cut trivial;
    trivial.push_back(Abc_ObjId(pObj));
    cuts[Abc_ObjId(pObj)].push_back(trivial);
  }

  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    Cut trivial;
    trivial.push_back(id);
    cuts[id].push_back(trivial);

    std::set<Cut> seen;
    seen.insert(trivial);

    const CutList& cuts0 = cuts[Abc_ObjId(Abc_ObjFanin0(pObj))];
    const CutList& cuts1 = cuts[Abc_ObjId(Abc_ObjFanin1(pObj))];
    for (const Cut& u : cuts0) {
      for (const Cut& v : cuts1) {
        Cut merged = MergeCuts(u, v);
        if ((int)merged.size() > k) {
          continue;
        }
        if (seen.insert(merged).second) {
          cuts[id].push_back(merged);
        }
      }
    }
    FilterDominatedCuts(cuts[id]);
  }
  return cuts;
}

uint64_t ComputeTruthTable(Abc_Ntk_t* pNtk, Abc_Obj_t* pRoot, const Cut& leaves) {
  int n = (int)leaves.size();
  std::unordered_set<int> leafSet(leaves.begin(), leaves.end());
  std::unordered_set<int> visited;
  std::vector<Abc_Obj_t*> cone;
  CollectCone(pRoot, leafSet, visited, cone);

  int constId = Abc_ObjId(Abc_AigConst1(pNtk));
  std::unordered_map<int, int> val;
  uint64_t tt = 0;
  int nPatterns = 1 << n;

  for (int mask = 0; mask < nPatterns; ++mask) {
    val.clear();
    val[constId] = 1;
    for (int i = 0; i < n; ++i) {
      int bit = (mask >> (n - 1 - i)) & 1;
      val[leaves[i]] = bit;
    }
    for (Abc_Obj_t* pNode : cone) {
      int v0 = val[Abc_ObjId(Abc_ObjFanin0(pNode))] ^ Abc_ObjFaninC0(pNode);
      int v1 = val[Abc_ObjId(Abc_ObjFanin1(pNode))] ^ Abc_ObjFaninC1(pNode);
      val[Abc_ObjId(pNode)] = v0 & v1;
    }
    if (val[Abc_ObjId(pRoot)]) {
      tt |= (uint64_t)1 << mask;
    }
  }
  return tt;
}

int ComputeBddSize(Abc_Ntk_t* pNtk, Abc_Obj_t* pRoot, const Cut& leaves) {
  int n = (int)leaves.size();
  DdManager* dd = Cudd_Init(n, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);

  std::unordered_set<int> leafSet(leaves.begin(), leaves.end());
  std::unordered_set<int> visited;
  std::vector<Abc_Obj_t*> cone;
  CollectCone(pRoot, leafSet, visited, cone);

  std::unordered_map<int, DdNode*> bddOf;
  bddOf[Abc_ObjId(Abc_AigConst1(pNtk))] = Cudd_ReadOne(dd);
  for (int i = 0; i < n; ++i) {
    bddOf[leaves[i]] = Cudd_bddIthVar(dd, i);
  }

  std::vector<DdNode*> toDeref;
  for (Abc_Obj_t* pNode : cone) {
    DdNode* b0 = Cudd_NotCond(bddOf[Abc_ObjId(Abc_ObjFanin0(pNode))],
                              Abc_ObjFaninC0(pNode));
    DdNode* b1 = Cudd_NotCond(bddOf[Abc_ObjId(Abc_ObjFanin1(pNode))],
                              Abc_ObjFaninC1(pNode));
    DdNode* res = Cudd_bddAnd(dd, b0, b1);
    Cudd_Ref(res);
    bddOf[Abc_ObjId(pNode)] = res;
    toDeref.push_back(res);
  }

  DdNode* rootBdd = bddOf[Abc_ObjId(pRoot)];
  int size = Cudd_DagSize(rootBdd);

  for (DdNode* node : toDeref) {
    Cudd_RecursiveDeref(dd, node);
  }
  Cudd_Quit(dd);
  return size;
}

void PrintCutPrefix(int nodeId, const Cut& cut) {
  printf("%d:", nodeId);
  for (int leaf : cut) {
    printf(" %d", leaf);
  }
}

void PrintCutsTt(Abc_Ntk_t* pNtk, int k) {
  std::vector<CutList> cuts = EnumerateCuts(pNtk, k);
  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const Cut& cut : cuts[id]) {
      uint64_t tt = ComputeTruthTable(pNtk, pObj, cut);
      PrintCutPrefix(id, cut);
      printf(": %llX\n", (unsigned long long)tt);
    }
  }
}

void PrintCutsBddSize(Abc_Ntk_t* pNtk, int k) {
  std::vector<CutList> cuts = EnumerateCuts(pNtk, k);
  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const Cut& cut : cuts[id]) {
      int size = ComputeBddSize(pNtk, pObj, cut);
      PrintCutPrefix(id, cut);
      printf(": %d\n", size);
    }
  }
}

int ParseKAndValidate(Abc_Frame_t* pAbc, int argc, char** argv, int* pK,
                      const char* cmdName) {
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        return -1;
      default:
        return -1;
    }
  }
  if (argc != globalUtilOptind + 1) {
    return -1;
  }
  *pK = atoi(argv[globalUtilOptind]);
  if (*pK < 2 || *pK > 6) {
    Abc_Print(-1, "k must be between 2 and 6.\n");
    return 1;
  }
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not an AIG. Please run \"strash\".\n");
    return 1;
  }
  (void)cmdName;
  return 0;
}

}  // namespace

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k = 0;
  int status = ParseKAndValidate(pAbc, argc, argv, &k, "lsv_cut_tt");
  if (status < 0) {
    Abc_Print(-2, "usage: lsv_cut_tt <k> [-h]\n");
    Abc_Print(-2, "\t        enumerate k-feasible cuts and print truth tables\n");
    Abc_Print(-2, "\t<k>   : cut size limit (2-6)\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  if (status > 0) {
    return 1;
  }
  PrintCutsTt(Abc_FrameReadNtk(pAbc), k);
  return 0;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k = 0;
  int status = ParseKAndValidate(pAbc, argc, argv, &k, "lsv_cut_bddsize");
  if (status < 0) {
    Abc_Print(-2, "usage: lsv_cut_bddsize <k> [-h]\n");
    Abc_Print(-2,
              "\t        enumerate k-feasible cuts and print ROBDD sizes\n");
    Abc_Print(-2, "\t<k>   : cut size limit (2-6)\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  if (status > 0) {
    return 1;
  }
  PrintCutsBddSize(Abc_FrameReadNtk(pAbc), k);
  return 0;
}
