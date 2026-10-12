/**
 * LSV PA1 - Exercise 4
 *   lsv_cut_tt      <k> : enumerate k-feasible cuts of every AND node and
 *                          print the truth table of each cut (hex).
 *   lsv_cut_bddsize <k> : enumerate k-feasible cuts of every AND node and
 *                          print the ROBDD size of each cut (Cudd_DagSize).
 *
 * The cut enumeration, truth-table simulation and BDD construction below are
 * written from scratch (no ABC built-in cut / truth-table / BDD builders).
 */
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <vector>

namespace {

typedef std::vector<int> Cut;  // node IDs, sorted ascending

// ---------------------------------------------------------------------------
// Cut enumeration
// ---------------------------------------------------------------------------
class CutEnumerator {
 public:
  CutEnumerator(Abc_Ntk_t* pNtk, int k) : k_(k) {
    cuts_.resize(Abc_NtkObjNumMax(pNtk));
    done_.assign(Abc_NtkObjNumMax(pNtk), false);
  }

  // All k-feasible cuts of pObj, trivial cut first, then in generation order.
  const std::vector<Cut>& cutsOf(Abc_Obj_t* pObj) {
    int id = Abc_ObjId(pObj);
    if (done_[id]) return cuts_[id];
    done_[id] = true;
    std::vector<Cut>& res = cuts_[id];
    res.push_back(Cut(1, id));  // trivial cut {id}
    // PIs (and the constant node) only have the trivial cut.
    if (!Abc_ObjIsNode(pObj) || Abc_ObjFaninNum(pObj) < 2) return res;

    const std::vector<Cut>& c0 = cutsOf(Abc_ObjFanin0(pObj));
    const std::vector<Cut>& c1 = cutsOf(Abc_ObjFanin1(pObj));
    std::vector<Cut> cand;
    std::vector<uint64_t> sig;  // bit (id % 64) signature of each candidate
    Cut u;
    for (size_t i = 0; i < c0.size(); ++i) {
      for (size_t j = 0; j < c1.size(); ++j) {
        mergeSorted(c0[i], c1[j], u);
        if ((int)u.size() > k_) continue;
        uint64_t su = signature(u);
        bool dup = false;
        for (size_t t = 0; t < cand.size() && !dup; ++t)
          dup = (sig[t] == su && cand[t] == u);
        if (dup) continue;
        cand.push_back(u);
        sig.push_back(su);
      }
    }
    // Remove dominated cuts (a cut that strictly contains another cut).
    for (size_t i = 0; i < cand.size(); ++i) {
      bool dominated = false;
      for (size_t j = 0; j < cand.size() && !dominated; ++j) {
        if (i == j || cand[j].size() >= cand[i].size()) continue;
        if ((sig[j] & ~sig[i]) != 0) continue;  // j has an ID that i lacks
        if (std::includes(cand[i].begin(), cand[i].end(), cand[j].begin(),
                          cand[j].end()))
          dominated = true;
      }
      if (!dominated) res.push_back(cand[i]);
    }
    return res;
  }

 private:
  static uint64_t signature(const Cut& c) {
    uint64_t s = 0;
    for (size_t i = 0; i < c.size(); ++i) s |= 1ULL << (c[i] & 63);
    return s;
  }
  static void mergeSorted(const Cut& a, const Cut& b, Cut& out) {
    out.clear();
    std::set_union(a.begin(), a.end(), b.begin(), b.end(),
                   std::back_inserter(out));
  }

  int k_;
  std::vector<std::vector<Cut> > cuts_;
  std::vector<bool> done_;
};

// ---------------------------------------------------------------------------
// Truth table of a node w.r.t. a cut (variables ordered as the cut, the first
// cut node is the most significant bit of the minterm index).
// ---------------------------------------------------------------------------
class TruthBuilder {
 public:
  explicit TruthBuilder(Abc_Ntk_t* pNtk)
      : memo_(Abc_NtkObjNumMax(pNtk), 0), stamp_(Abc_NtkObjNumMax(pNtk), 0),
        curStamp_(0) {}

  // Truth table of pRoot as a function of the cut leaves.
  uint64_t compute(Abc_Obj_t* pRoot, const Cut& cut) {
    cut_ = &cut;
    k_ = (int)cut.size();
    int nBits = 1 << k_;
    mask_ = (nBits >= 64) ? ~0ULL : ((1ULL << nBits) - 1);
    ++curStamp_;
    return build(pRoot) & mask_;
  }

 private:
  // Projection function of variable varIdx: variable varIdx has weight
  // 2^(k-1-varIdx) in the minterm index (first cut node = MSB).
  uint64_t leafTruth(int varIdx) const {
    static const uint64_t kProj[6] = {
        0xAAAAAAAAAAAAAAAAULL, 0xCCCCCCCCCCCCCCCCULL, 0xF0F0F0F0F0F0F0F0ULL,
        0xFF00FF00FF00FF00ULL, 0xFFFF0000FFFF0000ULL, 0xFFFFFFFF00000000ULL};
    return kProj[k_ - 1 - varIdx];  // weight 2^w  <->  kProj[w]
  }
  uint64_t build(Abc_Obj_t* pObj) {
    int id = Abc_ObjId(pObj);
    if (stamp_[id] == curStamp_) return memo_[id];
    uint64_t t;
    Cut::const_iterator pos = std::lower_bound(cut_->begin(), cut_->end(), id);
    if (pos != cut_->end() && *pos == id) {
      t = leafTruth((int)(pos - cut_->begin()));
    } else if (Abc_ObjFaninNum(pObj) < 2) {
      t = ~0ULL;  // constant-1 node (only reachable if it is in the cone)
    } else {
      uint64_t t0 = build(Abc_ObjFanin0(pObj));
      uint64_t t1 = build(Abc_ObjFanin1(pObj));
      if (Abc_ObjFaninC0(pObj)) t0 = ~t0;
      if (Abc_ObjFaninC1(pObj)) t1 = ~t1;
      t = t0 & t1;
    }
    t &= mask_;
    memo_[id] = t;
    stamp_[id] = curStamp_;
    return t;
  }

  const Cut* cut_;
  int k_;
  uint64_t mask_;
  std::vector<uint64_t> memo_;
  std::vector<unsigned> stamp_;
  unsigned curStamp_;
};

// ---------------------------------------------------------------------------
// ROBDD of a node w.r.t. a cut. BDD variable i <-> i-th cut node (sorted by
// ID), so smaller IDs are tested closer to the root. Reordering is disabled.
// ---------------------------------------------------------------------------
class BddBuilder {
 public:
  BddBuilder(DdManager* dd, Abc_Ntk_t* pNtk)
      : dd_(dd), memo_(Abc_NtkObjNumMax(pNtk), (DdNode*)NULL),
        stamp_(Abc_NtkObjNumMax(pNtk), 0), curStamp_(0) {}

  // ROBDD size (Cudd_DagSize) of pRoot as a function of the cut leaves.
  int size(Abc_Obj_t* pRoot, const Cut& cut) {
    cut_ = &cut;
    ++curStamp_;
    touched_.clear();
    DdNode* f = build(pRoot);
    int n = Cudd_DagSize(f);
    for (size_t i = 0; i < touched_.size(); ++i)
      Cudd_RecursiveDeref(dd_, memo_[touched_[i]]);
    return n;
  }

 private:
  DdNode* build(Abc_Obj_t* pObj) {
    int id = Abc_ObjId(pObj);
    if (stamp_[id] == curStamp_) return memo_[id];
    DdNode* f;
    Cut::const_iterator pos = std::lower_bound(cut_->begin(), cut_->end(), id);
    if (pos != cut_->end() && *pos == id) {
      f = Cudd_bddIthVar(dd_, (int)(pos - cut_->begin()));
    } else if (Abc_ObjFaninNum(pObj) < 2) {
      f = Cudd_ReadOne(dd_);
    } else {
      DdNode* f0 = build(Abc_ObjFanin0(pObj));
      DdNode* f1 = build(Abc_ObjFanin1(pObj));
      if (Abc_ObjFaninC0(pObj)) f0 = Cudd_Not(f0);
      if (Abc_ObjFaninC1(pObj)) f1 = Cudd_Not(f1);
      f = Cudd_bddAnd(dd_, f0, f1);
    }
    Cudd_Ref(f);
    memo_[id] = f;
    stamp_[id] = curStamp_;
    touched_.push_back(id);
    return f;
  }

  DdManager* dd_;
  const Cut* cut_;
  std::vector<DdNode*> memo_;
  std::vector<unsigned> stamp_;
  unsigned curStamp_;
  std::vector<int> touched_;
};

// ---------------------------------------------------------------------------
// Command bodies
// ---------------------------------------------------------------------------
void printCut(int rootId, const Cut& cut) {
  printf("%d: ", rootId);
  for (size_t i = 0; i < cut.size(); ++i)
    printf("%s%d", i ? " " : "", cut[i]);
  printf(": ");
}

int parseK(int argc, char** argv, const char* cmd) {
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    if (c == 'h') return -1;
    return -1;
  }
  if (globalUtilOptind + 1 != argc) {
    Abc_Print(-1, "%s: expected exactly one argument <k>.\n", cmd);
    return -1;
  }
  int k = atoi(argv[globalUtilOptind]);
  if (k < 1 || k > 6) {
    Abc_Print(-1, "%s: k must be between 1 and 6 (got %s).\n", cmd,
              argv[globalUtilOptind]);
    return -1;
  }
  return k;
}

Abc_Ntk_t* checkNtk(Abc_Frame_t* pAbc) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return NULL;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG (run \"strash\" first).\n");
    return NULL;
  }
  return pNtk;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k = parseK(argc, argv, "lsv_cut_tt");
  if (k < 0) {
    Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
    Abc_Print(-2, "\t        enumerates k-feasible cuts of every AND node and prints\n");
    Abc_Print(-2, "\t        the truth table (hex) of each cut\n");
    Abc_Print(-2, "\t<k>   : maximum cut size, 1 <= k <= 6\n");
    return 1;
  }
  Abc_Ntk_t* pNtk = checkNtk(pAbc);
  if (!pNtk) return 1;

  CutEnumerator enumerator(pNtk, k);
  TruthBuilder truth(pNtk);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    if (Abc_ObjFaninNum(pObj) < 2) continue;  // skip constant node
    const std::vector<Cut>& cuts = enumerator.cutsOf(pObj);
    for (size_t c = 0; c < cuts.size(); ++c) {
      uint64_t tt = truth.compute(pObj, cuts[c]);
      printCut(Abc_ObjId(pObj), cuts[c]);
      printf("%llX\n", (unsigned long long)tt);
    }
  }
  return 0;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k = parseK(argc, argv, "lsv_cut_bddsize");
  if (k < 0) {
    Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
    Abc_Print(-2, "\t        enumerates k-feasible cuts of every AND node and prints\n");
    Abc_Print(-2, "\t        the ROBDD size of each cut (variable order = node ID order)\n");
    Abc_Print(-2, "\t<k>   : maximum cut size, 1 <= k <= 6\n");
    return 1;
  }
  Abc_Ntk_t* pNtk = checkNtk(pAbc);
  if (!pNtk) return 1;

  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Cudd_AutodynDisable(dd);  // keep the fixed variable order

  CutEnumerator enumerator(pNtk, k);
  BddBuilder bdd(dd, pNtk);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    if (Abc_ObjFaninNum(pObj) < 2) continue;  // skip constant node
    const std::vector<Cut>& cuts = enumerator.cutsOf(pObj);
    for (size_t c = 0; c < cuts.size(); ++c) {
      int n = bdd.size(pObj, cuts[c]);
      printCut(Abc_ObjId(pObj), cuts[c]);
      printf("%d\n", n);
    }
  }
  Cudd_Quit(dd);
  return 0;
}

// ---------------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------------
void initCut(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
}
void destroyCut(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t cutFrameInitializer = {initCut, destroyCut};

struct CutPackageRegistrationManager {
  CutPackageRegistrationManager() {
    Abc_FrameAddInitializer(&cutFrameInitializer);
  }
} lsvCutPackageRegistrationManager;

}  // namespace
