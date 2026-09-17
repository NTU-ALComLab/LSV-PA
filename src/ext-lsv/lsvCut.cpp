#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

// Set to true to drop cuts that are supersets of another cut of the same node.
static const bool kRemoveDominatedCuts = false;

namespace {

const int kMaxCutSize = 6;

// A cut of a node: n leaf IDs stored in ascending order, plus a 64-bit
// signature (bit id%64 set for every leaf) used to reject most infeasible
// merges without touching the leaf arrays.
struct Cut {
  int n = 0;
  int v[kMaxCutSize] = {0, 0, 0, 0, 0, 0};
  uint64_t sig = 0;

  bool operator==(const Cut& o) const {
    if (n != o.n || sig != o.sig) return false;
    for (int i = 0; i < n; ++i)
      if (v[i] != o.v[i]) return false;
    return true;
  }
};

inline uint64_t LeafBit(int id) { return 1ULL << (id & 63); }

struct CutHash {
  size_t operator()(const Cut& c) const {
    uint64_t h = 1469598103934665603ULL;  // FNV-1a over the leaf IDs
    for (int i = 0; i < c.n; ++i) {
      h ^= static_cast<uint64_t>(c.v[i]);
      h *= 1099511628211ULL;
    }
    return static_cast<size_t>(h);
  }
};

typedef std::vector<Cut> CutList;

Cut TrivialCut(int id) {
  Cut c;
  c.n = 1;
  c.v[0] = id;
  c.sig = LeafBit(id);
  return c;
}

// Union of two sorted cuts. Returns false if the union has more than k leaves.
// The signature test is only a filter: distinct leaves may share a bit, so a
// small popcount does not prove feasibility, but a popcount above k does prove
// infeasibility, and that rejects the vast majority of pairs cheaply.
bool MergeCuts(const Cut& a, const Cut& b, int k, Cut& out) {
  out.sig = a.sig | b.sig;
  if (__builtin_popcountll(out.sig) > k) return false;
  int i = 0, j = 0;
  out.n = 0;
  while (i < a.n || j < b.n) {
    int x;
    if (j >= b.n) {
      x = a.v[i++];
    } else if (i >= a.n) {
      x = b.v[j++];
    } else if (a.v[i] < b.v[j]) {
      x = a.v[i++];
    } else if (b.v[j] < a.v[i]) {
      x = b.v[j++];
    } else {  // same leaf in both cuts
      x = a.v[i];
      ++i;
      ++j;
    }
    if (out.n == k) return false;
    out.v[out.n++] = x;
  }
  return true;
}

// Is a a subset of b? Both sorted.
bool IsSubset(const Cut& a, const Cut& b) {
  int j = 0;
  for (int i = 0; i < a.n; ++i) {
    while (j < b.n && b.v[j] < a.v[i]) ++j;
    if (j >= b.n || b.v[j] != a.v[i]) return false;
    ++j;
  }
  return true;
}

// Removes every cut that is a strict superset of another cut in the list,
// keeping the original order of the survivors.
void RemoveDominated(CutList& cuts) {
  CutList kept;
  for (size_t i = 0; i < cuts.size(); ++i) {
    bool dominated = false;
    for (size_t j = 0; j < cuts.size() && !dominated; ++j) {
      if (j == i || cuts[j].n >= cuts[i].n) continue;
      if ((cuts[j].sig & ~cuts[i].sig) != 0) continue;  // j has a leaf that i lacks
      dominated = IsSubset(cuts[j], cuts[i]);
    }
    if (!dominated) kept.push_back(cuts[i]);
  }
  cuts.swap(kept);
}

// Buffered stdout writer: one fwrite per 64 KB instead of one printf per field.
class OutBuf {
 public:
  ~OutBuf() { Flush(); }
  void PutChar(char c) {
    if (len_ == kSize) Flush();
    buf_[len_++] = c;
  }
  void PutInt(int x) {  // x >= 0
    char tmp[12];
    int n = 0;
    do {
      tmp[n++] = static_cast<char>('0' + x % 10);
      x /= 10;
    } while (x > 0);
    if (len_ + n > kSize) Flush();
    while (n > 0) buf_[len_++] = tmp[--n];
  }
  void PutHex(uint64_t x) {  // uppercase, no prefix, no leading zeros
    char tmp[17];
    int n = 0;
    do {
      tmp[n++] = "0123456789ABCDEF"[x & 15];
      x >>= 4;
    } while (x > 0);
    if (len_ + n > kSize) Flush();
    while (n > 0) buf_[len_++] = tmp[--n];
  }
  void Flush() {
    if (len_ > 0) fwrite(buf_, 1, len_, stdout);
    len_ = 0;
  }

 private:
  static const int kSize = 1 << 16;
  char buf_[kSize];
  int len_ = 0;
};

// Enumerates the k-feasible cuts of every AND node of a strashed AIG.
//
// Cuts are built bottom-up: a PI has only its trivial cut; an AND node has its
// trivial cut followed by the unions of every cut of fanin 0 with every cut of
// fanin 1 (outer loop over fanin 0), keeping unions with at most k leaves and
// dropping duplicates. This is the order shown in the assignment example.
//
// Cut lists are released as soon as every AND fanout of a node has been
// processed, so memory stays proportional to the current frontier rather than
// to the whole network.
class CutEnumerator {
 public:
  CutEnumerator(Abc_Ntk_t* pAig, int k)
      : pAig_(pAig), k_(k), cuts_(Abc_NtkObjNumMax(pAig)),
        done_(Abc_NtkObjNumMax(pAig), 0), pending_(Abc_NtkObjNumMax(pAig), 0) {
    Abc_Obj_t* pObj;
    Abc_Obj_t* pFanout;
    int i, j;
    Abc_NtkForEachObj(pAig, pObj, i) {
      int n = 0;
      Abc_ObjForEachFanout(pObj, pFanout, j) n += Abc_ObjIsNode(pFanout);
      pending_[Abc_ObjId(pObj)] = n;
    }
  }

  // Cut list of pObj, computing it (and, if needed, its fanins') on demand.
  const CutList& Compute(Abc_Obj_t* pObj) {
    int id = Abc_ObjId(pObj);
    if (done_[id]) return cuts_[id];
    CutList& out = cuts_[id];
    if (!Abc_ObjIsNode(pObj)) {  // PI or constant: only the trivial cut
      out.push_back(TrivialCut(id));
    } else {
      const CutList& c0 = Compute(Abc_ObjFanin0(pObj));
      const CutList& c1 = Compute(Abc_ObjFanin1(pObj));
      std::unordered_set<Cut, CutHash> seen;
      out.push_back(TrivialCut(id));
      seen.insert(out.back());
      Cut u;
      for (size_t a = 0; a < c0.size(); ++a) {
        for (size_t b = 0; b < c1.size(); ++b) {
          if (!MergeCuts(c0[a], c1[b], k_, u)) continue;
          if (!seen.insert(u).second) continue;  // duplicate
          out.push_back(u);
        }
      }
      if (kRemoveDominatedCuts) RemoveDominated(out);
    }
    done_[id] = 1;
    return out;
  }

  // Call after pObj has been fully handled: frees cut lists nobody needs anymore.
  void Release(Abc_Obj_t* pObj) {
    if (Abc_ObjIsNode(pObj)) {
      Drop(Abc_ObjFaninId0(pObj));
      Drop(Abc_ObjFaninId1(pObj));
    }
    if (pending_[Abc_ObjId(pObj)] == 0) Free(Abc_ObjId(pObj));
  }

 private:
  void Drop(int id) {
    if (--pending_[id] == 0) Free(id);
  }
  void Free(int id) { CutList().swap(cuts_[id]); }

  Abc_Ntk_t* pAig_;
  int k_;
  std::vector<CutList> cuts_;
  std::vector<char> done_;
  std::vector<int> pending_;
};

// Computes the truth table of a cut function by bit-parallel simulation.
//
// For a cut with m leaves (m <= 6) the 2^m input assignments are numbered
// 0 .. 2^m-1; leaf i (ascending ID order) is the most significant bit of the
// assignment index, and bit j of the result is the value of the root under
// assignment j. Each leaf gets the 64-bit pattern of its own variable, then
// the cone between the leaves and the root is evaluated once with AND and
// NOT on whole words. Nodes are visited once per cut using ABC's traversal
// IDs, so reconvergent cones are not re-evaluated.
class ConeSimulator {
 public:
  explicit ConeSimulator(Abc_Ntk_t* pAig)
      : pAig_(pAig), tt_(Abc_NtkObjNumMax(pAig), 0) {
    for (int m = 1; m <= kMaxCutSize; ++m) {
      mask_[m] = (m == 6) ? ~0ULL : ((1ULL << (1 << m)) - 1);
      for (int i = 0; i < m; ++i) {
        uint64_t p = 0;
        for (int j = 0; j < (1 << m); ++j)
          if ((j >> (m - 1 - i)) & 1) p |= 1ULL << j;
        pattern_[m][i] = p;
      }
    }
  }

  uint64_t Simulate(Abc_Obj_t* pRoot, const Cut& c) {
    Abc_NtkIncrementTravId(pAig_);
    for (int i = 0; i < c.n; ++i) {
      Abc_Obj_t* pLeaf = Abc_NtkObj(pAig_, c.v[i]);
      tt_[c.v[i]] = pattern_[c.n][i];
      Abc_NodeSetTravIdCurrent(pLeaf);
    }
    return Eval(pRoot, mask_[c.n]);
  }

 private:
  uint64_t Eval(Abc_Obj_t* pObj, uint64_t mask) {
    if (Abc_NodeIsTravIdCurrent(pObj)) return tt_[Abc_ObjId(pObj)];
    if (!Abc_ObjIsNode(pObj)) {
      // Only the constant node can be reached below a valid cut.
      return Abc_AigNodeIsConst(pObj) ? mask : 0;
    }
    uint64_t t0 = Eval(Abc_ObjFanin0(pObj), mask);
    uint64_t t1 = Eval(Abc_ObjFanin1(pObj), mask);
    if (Abc_ObjFaninC0(pObj)) t0 = ~t0 & mask;
    if (Abc_ObjFaninC1(pObj)) t1 = ~t1 & mask;
    uint64_t t = t0 & t1;
    tt_[Abc_ObjId(pObj)] = t;
    Abc_NodeSetTravIdCurrent(pObj);
    return t;
  }

  Abc_Ntk_t* pAig_;
  std::vector<uint64_t> tt_;
  uint64_t mask_[kMaxCutSize + 1];
  uint64_t pattern_[kMaxCutSize + 1][kMaxCutSize];
};

// Builds the ROBDD of a cut function with CUDD and returns its size.
//
// Leaf i of the cut (ascending ID order) is BDD variable i, so the leaf with
// the smallest ID is tested first, closest to the root, as the assignment
// requires. Dynamic reordering is disabled to keep that order. The cone
// between the leaves and the root is translated node by node with
// Cudd_bddAnd / Cudd_Not, again visiting each node once per cut via traversal
// IDs. Cudd_DagSize counts the nodes reachable from the root including the
// constant node. Intermediate results are dereferenced after each cut so the
// manager does not grow with the number of cuts.
class ConeBddBuilder {
 public:
  explicit ConeBddBuilder(Abc_Ntk_t* pAig)
      : pAig_(pAig), bdd_(Abc_NtkObjNumMax(pAig), NULL) {
    dd_ = Cudd_Init(kMaxCutSize, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    Cudd_AutodynDisable(dd_);
    for (int i = 0; i < kMaxCutSize; ++i) var_[i] = Cudd_bddIthVar(dd_, i);
  }
  ~ConeBddBuilder() { Cudd_Quit(dd_); }

  int Size(Abc_Obj_t* pRoot, const Cut& c) {
    Abc_NtkIncrementTravId(pAig_);
    for (int i = 0; i < c.n; ++i) {
      bdd_[c.v[i]] = var_[i];
      Abc_NodeSetTravIdCurrent(Abc_NtkObj(pAig_, c.v[i]));
    }
    built_.clear();
    DdNode* f = Build(pRoot);
    int size = Cudd_DagSize(f);
    for (size_t i = 0; i < built_.size(); ++i) Cudd_RecursiveDeref(dd_, built_[i]);
    return size;
  }

 private:
  DdNode* Build(Abc_Obj_t* pObj) {
    if (Abc_NodeIsTravIdCurrent(pObj)) return bdd_[Abc_ObjId(pObj)];
    if (!Abc_ObjIsNode(pObj)) {
      // Only the constant node can be reached below a valid cut.
      return Abc_AigNodeIsConst(pObj) ? Cudd_ReadOne(dd_) : Cudd_ReadLogicZero(dd_);
    }
    DdNode* f0 = Build(Abc_ObjFanin0(pObj));
    DdNode* f1 = Build(Abc_ObjFanin1(pObj));
    if (Abc_ObjFaninC0(pObj)) f0 = Cudd_Not(f0);
    if (Abc_ObjFaninC1(pObj)) f1 = Cudd_Not(f1);
    DdNode* f = Cudd_bddAnd(dd_, f0, f1);
    Cudd_Ref(f);
    built_.push_back(f);
    bdd_[Abc_ObjId(pObj)] = f;
    Abc_NodeSetTravIdCurrent(pObj);
    return f;
  }

  Abc_Ntk_t* pAig_;
  DdManager* dd_;
  DdNode* var_[kMaxCutSize];
  std::vector<DdNode*> bdd_;
  std::vector<DdNode*> built_;
};

// Writes "<id>: <leaf> <leaf> ...: " (the value follows).
void PutCutPrefix(OutBuf& out, int id, const Cut& c) {
  out.PutInt(id);
  out.PutChar(':');
  for (int i = 0; i < c.n; ++i) {
    out.PutChar(' ');
    out.PutInt(c.v[i]);
  }
  out.PutChar(':');
  out.PutChar(' ');
}

}  // namespace

// ---- lsv_cut_tt ----------------------------------------------------------
static void Lsv_NtkCutTt(Abc_Ntk_t* pAig, int k) {
  CutEnumerator enumr(pAig, k);
  ConeSimulator sim(pAig);
  OutBuf out;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pAig, pObj, i) {
    const CutList& cuts = enumr.Compute(pObj);
    for (size_t c = 0; c < cuts.size(); ++c) {
      PutCutPrefix(out, Abc_ObjId(pObj), cuts[c]);
      out.PutHex(sim.Simulate(pObj, cuts[c]));
      out.PutChar('\n');
    }
    enumr.Release(pObj);
  }
}

// ---- lsv_cut_bddsize -----------------------------------------------------
// The ROBDD of a cut function under a fixed variable order is canonical, so
// its size is determined by the truth table over the ordered leaves. The
// truth table is cheap to compute, so it is used as a memo key: the BDD is
// built (from the cone, with CUDD) only the first time a given function of a
// given arity is met. Millions of cuts on the larger benchmarks share a few
// thousand distinct functions.
static void Lsv_NtkCutBddSize(Abc_Ntk_t* pAig, int k) {
  CutEnumerator enumr(pAig, k);
  ConeSimulator sim(pAig);
  ConeBddBuilder bdd(pAig);
  std::unordered_map<uint64_t, int> memo[kMaxCutSize + 1];  // per cut size
  OutBuf out;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pAig, pObj, i) {
    const CutList& cuts = enumr.Compute(pObj);
    for (size_t c = 0; c < cuts.size(); ++c) {
      const Cut& cut = cuts[c];
      uint64_t tt = sim.Simulate(pObj, cut);
      std::unordered_map<uint64_t, int>& table = memo[cut.n];
      std::unordered_map<uint64_t, int>::iterator it = table.find(tt);
      int size;
      if (it != table.end()) {
        size = it->second;
      } else {
        size = bdd.Size(pObj, cut);
        table[tt] = size;
      }
      PutCutPrefix(out, Abc_ObjId(pObj), cut);
      out.PutInt(size);
      out.PutChar('\n');
    }
    enumr.Release(pObj);
  }
}

// ---- shared argument handling: returns k, or -1 after printing an error/usage ----
static int Lsv_ParseCutArgs(Abc_Frame_t* pAbc, int argc, char** argv,
                            const char* cmdName, Abc_Ntk_t** ppNtk) {
  int c, k;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
      default:
        goto usage;
    }
  }
  if (argc != globalUtilOptind + 1) goto usage;  // exactly one positional <k>
  k = atoi(argv[globalUtilOptind]);
  if (k < 1 || k > kMaxCutSize) {
    Abc_Print(-1, "k must be between 1 and %d.\n", kMaxCutSize);
    return -1;
  }
  *ppNtk = Abc_FrameReadNtk(pAbc);
  if (*ppNtk == NULL) {
    Abc_Print(-1, "Empty network.\n");
    return -1;
  }
  if (!Abc_NtkIsStrash(*ppNtk) && !Abc_NtkIsLogic(*ppNtk)) {
    Abc_Print(-1, "This command expects an AIG (run \"strash\") or a logic network.\n");
    return -1;
  }
  return k;

usage:
  Abc_Print(-2, "usage: %s [-h] <k>\n", cmdName);
  Abc_Print(-2, "\t        enumerates k-feasible cuts of every AND node\n");
  Abc_Print(-2, "\t<k>   : maximum cut size (1..%d)\n", kMaxCutSize);
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return -1;
}

// Returns the AIG to work on. If the current network is already strashed it is
// returned as is (*pOwned = false). Otherwise a strashed copy is built with the
// same parameters as the "strash" command (fAllNodes = 0, fCleanup = 1,
// fRecord = 0), so node IDs match what "strash" would produce; the caller must
// free it (*pOwned = true). Strashing is done on a duplicate because
// Abc_NtkStrash converts the node functions of its input network in place,
// which would otherwise change the representation of the current network.
static Abc_Ntk_t* Lsv_GetAig(Abc_Ntk_t* pNtk, bool* pOwned) {
  if (Abc_NtkIsStrash(pNtk)) {
    *pOwned = false;
    return pNtk;
  }
  *pOwned = true;
  Abc_Ntk_t* pDup = Abc_NtkDup(pNtk);
  if (pDup == NULL) return NULL;
  Abc_Ntk_t* pAig = Abc_NtkStrash(pDup, 0, 1, 0);
  Abc_NtkDelete(pDup);
  return pAig;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk;
  int k = Lsv_ParseCutArgs(pAbc, argc, argv, "lsv_cut_tt", &pNtk);
  if (k < 0) return 1;
  bool owned;
  Abc_Ntk_t* pAig = Lsv_GetAig(pNtk, &owned);
  if (pAig == NULL) {
    Abc_Print(-1, "Strashing the network failed.\n");
    return 1;
  }
  Lsv_NtkCutTt(pAig, k);
  if (owned) Abc_NtkDelete(pAig);
  return 0;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk;
  int k = Lsv_ParseCutArgs(pAbc, argc, argv, "lsv_cut_bddsize", &pNtk);
  if (k < 0) return 1;
  bool owned;
  Abc_Ntk_t* pAig = Lsv_GetAig(pNtk, &owned);
  if (pAig == NULL) {
    Abc_Print(-1, "Strashing the network failed.\n");
    return 1;
  }
  Lsv_NtkCutBddSize(pAig, k);
  if (owned) Abc_NtkDelete(pAig);
  return 0;
}
