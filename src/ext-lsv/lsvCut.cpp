#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <cstdint>
#include <inttypes.h>
#include <vector>

namespace {

struct Lsv_Cut {
  std::vector<int> leaves;  // sorted ascending
  uint64_t tt;              // truth table (for lsv_cut_tt)
  DdNode* bdd;              // ROBDD (for lsv_cut_bddsize); may be NULL
};

static int Lsv_FindLeafPos(const std::vector<int>& leaves, int id) {
  for (int i = 0; i < (int)leaves.size(); i++) {
    if (leaves[i] == id) return i;
  }
  return -1;
}

// Leaf order matches cut listing left-to-right; rightmost leaf toggles fastest
// (LSB of the assignment index).
static int Lsv_LeafValue(uint64_t assign, int leafIdx, int nLeaves) {
  return (int)((assign >> (nLeaves - 1 - leafIdx)) & 1ULL);
}

static int Lsv_LocalAssign(const Lsv_Cut& cut, const std::vector<int>& merged,
                           uint64_t assign, int nMerged) {
  int n = (int)cut.leaves.size();
  int local = 0;
  for (int j = 0; j < n; j++) {
    int pos = Lsv_FindLeafPos(merged, cut.leaves[j]);
    int val = Lsv_LeafValue(assign, pos, nMerged);
    local |= (val << (n - 1 - j));
  }
  return local;
}

static uint64_t Lsv_MergeTruth(const Lsv_Cut& c0, const Lsv_Cut& c1,
                               int fCompl0, int fCompl1,
                               const std::vector<int>& merged) {
  int n = (int)merged.size();
  uint64_t tt = 0;
  uint64_t nPat = 1ULL << n;
  for (uint64_t a = 0; a < nPat; a++) {
    int bit0 = (int)((c0.tt >> Lsv_LocalAssign(c0, merged, a, n)) & 1ULL);
    int bit1 = (int)((c1.tt >> Lsv_LocalAssign(c1, merged, a, n)) & 1ULL);
    if (fCompl0) bit0 ^= 1;
    if (fCompl1) bit1 ^= 1;
    if (bit0 & bit1) tt |= (1ULL << a);
  }
  return tt;
}

static DdNode* Lsv_MergeBdd(DdManager* dd, const Lsv_Cut& c0, const Lsv_Cut& c1,
                            int fCompl0, int fCompl1) {
  DdNode* f0 = c0.bdd;
  DdNode* f1 = c1.bdd;
  if (fCompl0) f0 = Cudd_Not(f0);
  if (fCompl1) f1 = Cudd_Not(f1);
  DdNode* fand = Cudd_bddAnd(dd, f0, f1);
  Cudd_Ref(fand);
  return fand;
}

static bool Lsv_MergeLeaves(const std::vector<int>& a, const std::vector<int>& b,
                            int k, std::vector<int>& out) {
  out.clear();
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
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] == b[j]) {
      i++;
      j++;
    } else if (a[i] > b[j]) {
      j++;
    } else {
      return false;
    }
  }
  return i == a.size();
}

// Filter dominated cuts; if dd != NULL, deref BDDs of removed cuts.
static void Lsv_FilterDominated(DdManager* dd, std::vector<Lsv_Cut>& cuts) {
  std::vector<char> remove(cuts.size(), 0);
  for (size_t i = 0; i < cuts.size(); i++) {
    if (remove[i]) continue;
    for (size_t j = 0; j < cuts.size(); j++) {
      if (i == j || remove[j]) continue;
      if (cuts[i].leaves == cuts[j].leaves) {
        if (j > i) remove[j] = 1;
        continue;
      }
      if (cuts[i].leaves.size() < cuts[j].leaves.size() &&
          Lsv_IsSubset(cuts[i].leaves, cuts[j].leaves)) {
        remove[j] = 1;
      } else if (cuts[j].leaves.size() < cuts[i].leaves.size() &&
                 Lsv_IsSubset(cuts[j].leaves, cuts[i].leaves)) {
        remove[i] = 1;
        break;
      }
    }
  }
  std::vector<Lsv_Cut> kept;
  kept.reserve(cuts.size());
  for (size_t i = 0; i < cuts.size(); i++) {
    if (!remove[i]) {
      kept.push_back(cuts[i]);
    } else if (dd && cuts[i].bdd) {
      Cudd_RecursiveDeref(dd, cuts[i].bdd);
    }
  }
  cuts.swap(kept);
}

enum Lsv_CutMode { LSV_CUT_TT = 0, LSV_CUT_BDD = 1 };

static void Lsv_NtkCutEnum(Abc_Ntk_t* pNtk, int k, Lsv_CutMode mode) {
  int nObjs = Abc_NtkObjNumMax(pNtk);
  std::vector<std::vector<Lsv_Cut> > nodeCuts(nObjs);

  DdManager* dd = NULL;
  if (mode == LSV_CUT_BDD) {
    // Variable index == AIG node ID so smaller IDs are closer to the root.
    dd = Cudd_Init(nObjs, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    Cudd_AutodynDisable(dd);
  }

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachCi(pNtk, pObj, i) {
    Lsv_Cut cut;
    cut.leaves.push_back((int)Abc_ObjId(pObj));
    cut.tt = 2;
    cut.bdd = NULL;
    if (dd) {
      cut.bdd = Cudd_bddIthVar(dd, (int)Abc_ObjId(pObj));
      Cudd_Ref(cut.bdd);
    }
    nodeCuts[Abc_ObjId(pObj)].push_back(cut);
  }

  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = (int)Abc_ObjId(pObj);
    int id0 = (int)Abc_ObjId(Abc_ObjFanin0(pObj));
    int id1 = (int)Abc_ObjId(Abc_ObjFanin1(pObj));
    int fCompl0 = Abc_ObjFaninC0(pObj);
    int fCompl1 = Abc_ObjFaninC1(pObj);

    std::vector<Lsv_Cut>& cuts = nodeCuts[id];

    Lsv_Cut triv;
    triv.leaves.push_back(id);
    triv.tt = 2;
    triv.bdd = NULL;
    if (dd) {
      triv.bdd = Cudd_bddIthVar(dd, id);
      Cudd_Ref(triv.bdd);
    }
    cuts.push_back(triv);

    const std::vector<Lsv_Cut>& cuts0 = nodeCuts[id0];
    const std::vector<Lsv_Cut>& cuts1 = nodeCuts[id1];
    for (const Lsv_Cut& c0 : cuts0) {
      for (const Lsv_Cut& c1 : cuts1) {
        std::vector<int> merged;
        if (!Lsv_MergeLeaves(c0.leaves, c1.leaves, k, merged)) continue;
        Lsv_Cut cut;
        cut.leaves = merged;
        cut.tt = 0;
        cut.bdd = NULL;
        if (mode == LSV_CUT_TT) {
          cut.tt = Lsv_MergeTruth(c0, c1, fCompl0, fCompl1, merged);
        } else {
          cut.bdd = Lsv_MergeBdd(dd, c0, c1, fCompl0, fCompl1);
        }
        cuts.push_back(cut);
      }
    }

    Lsv_FilterDominated(dd, cuts);

    for (const Lsv_Cut& cut : cuts) {
      printf("%d:", id);
      for (int leaf : cut.leaves) printf(" %d", leaf);
      if (mode == LSV_CUT_TT) {
        printf(": %" PRIX64 "\n", (uint64_t)cut.tt);
      } else {
        printf(": %d\n", Cudd_DagSize(cut.bdd));
      }
    }
  }

  if (dd) {
    for (int n = 0; n < nObjs; n++) {
      for (Lsv_Cut& cut : nodeCuts[n]) {
        if (cut.bdd) Cudd_RecursiveDeref(dd, cut.bdd);
      }
    }
    Cudd_Quit(dd);
  }
}

}  // namespace

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
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
    Abc_Print(-1, "LSV_cut_tt: only works for structurally hashed AIGs (run \"strash\").\n");
    return 1;
  }
  {
    int k = atoi(argv[globalUtilOptind]);
    if (k < 2 || k > 6) {
      Abc_Print(-1, "LSV_cut_tt: k must be in [2, 6].\n");
      return 1;
    }
    Lsv_NtkCutEnum(pNtk, k, LSV_CUT_TT);
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt <k> [-h]\n");
  Abc_Print(-2, "\t        enumerate k-feasible cuts and print truth tables\n");
  Abc_Print(-2, "\t<k>   : cut size limit (2 <= k <= 6)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
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
    Abc_Print(-1, "LSV_cut_bddsize: only works for structurally hashed AIGs (run \"strash\").\n");
    return 1;
  }
  {
    int k = atoi(argv[globalUtilOptind]);
    if (k < 2 || k > 6) {
      Abc_Print(-1, "LSV_cut_bddsize: k must be in [2, 6].\n");
      return 1;
    }
    Lsv_NtkCutEnum(pNtk, k, LSV_CUT_BDD);
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize <k> [-h]\n");
  Abc_Print(-2, "\t        enumerate k-feasible cuts and print ROBDD sizes\n");
  Abc_Print(-2, "\t<k>   : cut size limit (2 <= k <= 6)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
