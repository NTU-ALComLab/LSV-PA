#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#endif

#include <cstdint>
#include <vector>

namespace {

struct Lsv_Cut {
  std::vector<int> leaves;  // sorted ascending
  uint64_t tt;              // MSB of assignment = first leaf
};

using Lsv_CutList = std::vector<Lsv_Cut>;

#ifdef ABC_USE_CUDD
struct Lsv_BddCut {
  std::vector<int> leaves;
  DdNode* bdd;
};

using Lsv_BddCutList = std::vector<Lsv_BddCut>;
#endif

static inline uint64_t Lsv_TtMask(int nVars) {
  if (nVars <= 0) return 1ULL;
  if (nVars >= 6) return ~0ULL;
  return (1ULL << (1 << nVars)) - 1ULL;
}

static inline uint64_t Lsv_TtNot(uint64_t tt, int nVars) {
  return tt ^ Lsv_TtMask(nVars);
}

// Stretch tt (over src leaves) onto dst leaf order.
// Assignment index uses first leaf as MSB (matches PA encoding).
static uint64_t Lsv_TtStretch(uint64_t tt, const std::vector<int>& src,
                              const std::vector<int>& dst) {
  const int nSrc = (int)src.size();
  const int nDst = (int)dst.size();
  if (nSrc == 0) {
    // Constant function: tt is 0 or 1.
    return (tt & 1ULL) ? Lsv_TtMask(nDst) : 0ULL;
  }
  if (nSrc == nDst) return tt;

  int pos[8];
  for (int i = 0; i < nSrc; i++) {
    pos[i] = -1;
    for (int j = 0; j < nDst; j++) {
      if (dst[j] == src[i]) {
        pos[i] = j;
        break;
      }
    }
  }

  uint64_t res = 0;
  const int nMasks = 1 << nDst;
  for (int m = 0; m < nMasks; m++) {
    int srcIdx = 0;
    for (int i = 0; i < nSrc; i++) {
      const int bit = (m >> (nDst - 1 - pos[i])) & 1;
      srcIdx |= bit << (nSrc - 1 - i);
    }
    if ((tt >> srcIdx) & 1ULL) res |= 1ULL << m;
  }
  return res;
}

static bool Lsv_MergeLeaves(const std::vector<int>& a, const std::vector<int>& b,
                            int k, std::vector<int>& out) {
  out.clear();
  out.reserve(a.size() + b.size());
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] == b[j]) {
      out.push_back(a[i]);
      i++;
      j++;
    } else if (a[i] < b[j]) {
      out.push_back(a[i++]);
    } else {
      out.push_back(b[j++]);
    }
    if ((int)out.size() > k) return false;
  }
  while (i < a.size()) {
    out.push_back(a[i++]);
    if ((int)out.size() > k) return false;
  }
  while (j < b.size()) {
    out.push_back(b[j++]);
    if ((int)out.size() > k) return false;
  }
  return true;
}

static bool Lsv_IsSubset(const std::vector<int>& a, const std::vector<int>& b) {
  // Is a a subset of b? (both sorted)
  if (a.size() > b.size()) return false;
  size_t j = 0;
  for (size_t i = 0; i < a.size(); i++) {
    while (j < b.size() && b[j] < a[i]) j++;
    if (j == b.size() || b[j] != a[i]) return false;
    j++;
  }
  return true;
}

static void Lsv_FilterDominated(Lsv_CutList& cuts) {
  std::vector<char> dead(cuts.size(), 0);
  for (size_t i = 0; i < cuts.size(); i++) {
    if (dead[i]) continue;
    for (size_t j = 0; j < cuts.size(); j++) {
      if (i == j || dead[j]) continue;
      if (cuts[i].leaves.size() == cuts[j].leaves.size()) continue;
      if (Lsv_IsSubset(cuts[i].leaves, cuts[j].leaves))
        dead[j] = 1;  // i dominates j
      else if (Lsv_IsSubset(cuts[j].leaves, cuts[i].leaves))
        dead[i] = 1;  // j dominates i
    }
  }
  Lsv_CutList kept;
  kept.reserve(cuts.size());
  for (size_t i = 0; i < cuts.size(); i++) {
    if (!dead[i]) kept.push_back(std::move(cuts[i]));
  }
  cuts.swap(kept);
}

static bool Lsv_HasSameLeaves(const Lsv_CutList& cuts,
                              const std::vector<int>& leaves) {
  for (const auto& c : cuts) {
    if (c.leaves == leaves) return true;
  }
  return false;
}

static void Lsv_AddCut(Lsv_CutList& cuts, std::vector<int> leaves, uint64_t tt) {
  if (Lsv_HasSameLeaves(cuts, leaves)) return;
  Lsv_Cut c;
  c.leaves = std::move(leaves);
  c.tt = tt & Lsv_TtMask((int)c.leaves.size());
  cuts.push_back(std::move(c));
}

static void Lsv_PrintCut(int rootId, const Lsv_Cut& cut) {
  printf("%d:", rootId);
  if (cut.leaves.empty()) {
    printf(" :");
  } else {
    for (int id : cut.leaves) printf(" %d", id);
    printf(":");
  }
  printf(" %llX\n", (unsigned long long)cut.tt);
}

static void Lsv_NtkCutTruth(Abc_Ntk_t* pNtk, int k) {
  const int nObjs = Abc_NtkObjNumMax(pNtk);
  std::vector<Lsv_CutList> cuts((size_t)nObjs);

  // Constant 1: empty cut, TT = 1.
  {
    Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
    Lsv_AddCut(cuts[Abc_ObjId(pConst)], {}, 1ULL);
  }

  // Primary inputs: trivial cut only (not printed).
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachCi(pNtk, pObj, i) {
    const int id = Abc_ObjId(pObj);
    Lsv_AddCut(cuts[id], {id}, 2ULL);  // identity
  }

  // AND nodes in topological order.
  Abc_AigForEachAnd(pNtk, pObj, i) {
    const int id = Abc_ObjId(pObj);
    Abc_Obj_t* pF0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* pF1 = Abc_ObjFanin1(pObj);
    const int c0 = Abc_ObjFaninC0(pObj);
    const int c1 = Abc_ObjFaninC1(pObj);
    const Lsv_CutList& cuts0 = cuts[Abc_ObjId(pF0)];
    const Lsv_CutList& cuts1 = cuts[Abc_ObjId(pF1)];

    Lsv_CutList& mine = cuts[id];
    mine.clear();

    // Trivial cut.
    Lsv_AddCut(mine, {id}, 2ULL);

    std::vector<int> merged;
    for (const auto& a : cuts0) {
      for (const auto& b : cuts1) {
        if (!Lsv_MergeLeaves(a.leaves, b.leaves, k, merged)) continue;

        uint64_t tt0 = Lsv_TtStretch(a.tt, a.leaves, merged);
        uint64_t tt1 = Lsv_TtStretch(b.tt, b.leaves, merged);
        const int n = (int)merged.size();
        if (c0) tt0 = Lsv_TtNot(tt0, n);
        if (c1) tt1 = Lsv_TtNot(tt1, n);
        Lsv_AddCut(mine, merged, tt0 & tt1);
      }
    }

    Lsv_FilterDominated(mine);

    // Print trivial cut first; keep remaining cuts in discovery order.
    for (const auto& cut : mine) {
      if (cut.leaves.size() == 1 && cut.leaves[0] == id) Lsv_PrintCut(id, cut);
    }
    for (const auto& cut : mine) {
      if (!(cut.leaves.size() == 1 && cut.leaves[0] == id))
        Lsv_PrintCut(id, cut);
    }
  }
}

#ifdef ABC_USE_CUDD

static bool Lsv_HasSameLeavesBdd(const Lsv_BddCutList& cuts,
                                 const std::vector<int>& leaves) {
  for (const auto& c : cuts) {
    if (c.leaves == leaves) return true;
  }
  return false;
}

static void Lsv_AddBddCut(DdManager* dd, Lsv_BddCutList& cuts,
                          std::vector<int> leaves, DdNode* bdd) {
  if (Lsv_HasSameLeavesBdd(cuts, leaves)) {
    Cudd_RecursiveDeref(dd, bdd);
    return;
  }
  Lsv_BddCut c;
  c.leaves = std::move(leaves);
  c.bdd = bdd;
  cuts.push_back(std::move(c));
}

static void Lsv_FilterDominatedBdd(DdManager* dd, Lsv_BddCutList& cuts) {
  std::vector<char> dead(cuts.size(), 0);
  for (size_t i = 0; i < cuts.size(); i++) {
    if (dead[i]) continue;
    for (size_t j = 0; j < cuts.size(); j++) {
      if (i == j || dead[j]) continue;
      if (cuts[i].leaves.size() == cuts[j].leaves.size()) continue;
      if (Lsv_IsSubset(cuts[i].leaves, cuts[j].leaves))
        dead[j] = 1;
      else if (Lsv_IsSubset(cuts[j].leaves, cuts[i].leaves))
        dead[i] = 1;
    }
  }
  Lsv_BddCutList kept;
  kept.reserve(cuts.size());
  for (size_t i = 0; i < cuts.size(); i++) {
    if (!dead[i])
      kept.push_back(std::move(cuts[i]));
    else
      Cudd_RecursiveDeref(dd, cuts[i].bdd);
  }
  cuts.swap(kept);
}

static void Lsv_PrintBddCut(int rootId, const Lsv_BddCut& cut) {
  printf("%d:", rootId);
  if (cut.leaves.empty()) {
    printf(" :");
  } else {
    for (int id : cut.leaves) printf(" %d", id);
    printf(":");
  }
  printf(" %d\n", Cudd_DagSize(cut.bdd));
}

static void Lsv_DerefBddCuts(DdManager* dd, Lsv_BddCutList& cuts) {
  for (auto& c : cuts) Cudd_RecursiveDeref(dd, c.bdd);
  cuts.clear();
}

static void Lsv_NtkCutBddSize(Abc_Ntk_t* pNtk, int k) {
  const int nObjs = Abc_NtkObjNumMax(pNtk);
  DdManager* dd =
      Cudd_Init(nObjs, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Cudd_AutodynDisable(dd);

  std::vector<Lsv_BddCutList> cuts((size_t)nObjs);

  // Constant 1: empty cut, BDD = constant 1.
  {
    Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
    DdNode* one = Cudd_ReadOne(dd);
    Cudd_Ref(one);
    Lsv_AddBddCut(dd, cuts[Abc_ObjId(pConst)], {}, one);
  }

  // Primary inputs: trivial cut (not printed).
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachCi(pNtk, pObj, i) {
    const int id = Abc_ObjId(pObj);
    DdNode* var = Cudd_bddIthVar(dd, id);
    Cudd_Ref(var);
    Lsv_AddBddCut(dd, cuts[id], {id}, var);
  }

  Abc_AigForEachAnd(pNtk, pObj, i) {
    const int id = Abc_ObjId(pObj);
    Abc_Obj_t* pF0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* pF1 = Abc_ObjFanin1(pObj);
    const int c0 = Abc_ObjFaninC0(pObj);
    const int c1 = Abc_ObjFaninC1(pObj);
    const Lsv_BddCutList& cuts0 = cuts[Abc_ObjId(pF0)];
    const Lsv_BddCutList& cuts1 = cuts[Abc_ObjId(pF1)];

    Lsv_BddCutList& mine = cuts[id];
    mine.clear();

    // Trivial cut: variable = this node's ID (smaller IDs closer to root).
    {
      DdNode* var = Cudd_bddIthVar(dd, id);
      Cudd_Ref(var);
      Lsv_AddBddCut(dd, mine, {id}, var);
    }

    std::vector<int> merged;
    for (const auto& a : cuts0) {
      for (const auto& b : cuts1) {
        if (!Lsv_MergeLeaves(a.leaves, b.leaves, k, merged)) continue;
        DdNode* f0 = Cudd_NotCond(a.bdd, c0);
        DdNode* f1 = Cudd_NotCond(b.bdd, c1);
        DdNode* f = Cudd_bddAnd(dd, f0, f1);
        if (f == nullptr) {
          Abc_Print(-1, "BDD AND failed (out of memory?).\n");
          continue;
        }
        Cudd_Ref(f);
        Lsv_AddBddCut(dd, mine, merged, f);
      }
    }

    Lsv_FilterDominatedBdd(dd, mine);

    for (const auto& cut : mine) {
      if (cut.leaves.size() == 1 && cut.leaves[0] == id)
        Lsv_PrintBddCut(id, cut);
    }
    for (const auto& cut : mine) {
      if (!(cut.leaves.size() == 1 && cut.leaves[0] == id))
        Lsv_PrintBddCut(id, cut);
    }
  }

  for (auto& list : cuts) Lsv_DerefBddCuts(dd, list);
  Cudd_Quit(dd);
}

#endif  // ABC_USE_CUDD

}  // namespace

extern "C" int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (argc != globalUtilOptind + 1) goto usage;
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "LSV cut tt works only for AIGs (run \"strash\").\n");
    return 1;
  }

  {
    char* end = nullptr;
    long k = strtol(argv[globalUtilOptind], &end, 10);
    if (end == argv[globalUtilOptind] || *end != '\0' || k < 1 || k > 6) {
      Abc_Print(-1, "Invalid k (expect integer in [1,6]).\n");
      return 1;
    }
    Lsv_NtkCutTruth(pNtk, (int)k);
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt <k> [-h]\n");
  Abc_Print(-2,
            "\t        enumerate k-feasible cuts and print truth tables\n");
  Abc_Print(-2, "\t<k>   : cut size limit (1..6)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

extern "C" int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (argc != globalUtilOptind + 1) goto usage;
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "LSV cut bddsize works only for AIGs (run \"strash\").\n");
    return 1;
  }

#ifndef ABC_USE_CUDD
  Abc_Print(-1, "ABC was built without CUDD; lsv_cut_bddsize unavailable.\n");
  return 1;
#else
  {
    char* end = nullptr;
    long k = strtol(argv[globalUtilOptind], &end, 10);
    if (end == argv[globalUtilOptind] || *end != '\0' || k < 1 || k > 6) {
      Abc_Print(-1, "Invalid k (expect integer in [1,6]).\n");
      return 1;
    }
    Lsv_NtkCutBddSize(pNtk, (int)k);
  }
  return 0;
#endif

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize <k> [-h]\n");
  Abc_Print(-2,
            "\t        enumerate k-feasible cuts and print ROBDD sizes\n");
  Abc_Print(-2, "\t<k>   : cut size limit (1..6)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
