#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <unordered_map>
#include <vector>
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdio>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBDDSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt",      Lsv_CommandCutTT,      0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize",  Lsv_CommandCutBDDSize, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// -----------------------------------------------------------------------
// lsv_print_nodes (original)
// -----------------------------------------------------------------------

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s, compl=%d\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin), Abc_ObjFaninC(pObj, j));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

// -----------------------------------------------------------------------
// Cut enumeration
// A cut stores its sorted leaf IDs and the truth table of the root over
// those leaves. The first (smallest-ID) leaf is the most significant bit of
// the input assignment; the output for assignment 00...0 is the LSB.
// -----------------------------------------------------------------------

static const int kMaxCutSize = 6;

struct Cut {
  uint64_t tt;
  uint64_t sign;  // bit (id % 64) set for every leaf; for fast filtering
  int nLeaves;
  int leaves[kMaxCutSize];
};
using CutSet = std::vector<Cut>;

static inline uint64_t leafSign(int id) { return uint64_t(1) << (id % 64); }

static inline uint64_t ttMask(int nVars) {
  return nVars >= 6 ? ~uint64_t(0) : ((uint64_t(1) << (1 << nVars)) - 1);
}

static Cut makeLeafCut(int id) {
  Cut c;
  c.tt = 0x2;
  c.sign = leafSign(id);
  c.nLeaves = 1;
  c.leaves[0] = id;
  return c;
}

// Sorted union of the leaves of a and b; returns false if it exceeds k.
static bool mergeLeaves(const Cut& a, const Cut& b, int k, Cut& out) {
  int i = 0, j = 0, n = 0;
  while (i < a.nLeaves || j < b.nLeaves) {
    if (n == k) return false;
    if (j == b.nLeaves || (i < a.nLeaves && a.leaves[i] < b.leaves[j]))
      out.leaves[n++] = a.leaves[i++];
    else if (i == a.nLeaves || b.leaves[j] < a.leaves[i])
      out.leaves[n++] = b.leaves[j++];
    else
      out.leaves[n++] = a.leaves[i++], j++;
  }
  out.nLeaves = n;
  return true;
}

// Is every leaf of a also a leaf of b?
static bool isSubset(const Cut& a, const Cut& b) {
  if ((a.sign & ~b.sign) != 0 || a.nLeaves > b.nLeaves) return false;
  int j = 0;
  for (int i = 0; i < a.nLeaves; ++i) {
    while (j < b.nLeaves && b.leaves[j] < a.leaves[i]) ++j;
    if (j == b.nLeaves || b.leaves[j] != a.leaves[i]) return false;
  }
  return true;
}

// Re-express the truth table of `from` over the leaves of its superset `to`.
static uint64_t ttExpand(const Cut& from, const Cut& to) {
  int shift[kMaxCutSize];  // input-assignment bit of each `from` leaf in `to`
  for (int i = 0, j = 0; i < from.nLeaves; ++i) {
    while (to.leaves[j] != from.leaves[i]) ++j;
    shift[i] = to.nLeaves - 1 - j;
  }
  uint64_t res = 0;
  for (int p = 0; p < (1 << to.nLeaves); ++p) {
    int q = 0;
    for (int i = 0; i < from.nLeaves; ++i)
      q = (q << 1) | ((p >> shift[i]) & 1);
    res |= ((from.tt >> q) & 1) << p;
  }
  return res;
}

// Truth table of pObj over the leaves of `cut` by bit-parallel simulation of
// the cone, treating every leaf as a free variable (traversal stops at
// leaves). Needed when a leaf lies inside the cone of another leaf, which
// only happens for cuts that contain a smaller cut.
static uint64_t simulateCone(Abc_Obj_t* pObj, const Cut& cut,
                             std::unordered_map<int, uint64_t>& memo) {
  auto it = memo.find(Abc_ObjId(pObj));
  if (it != memo.end()) return it->second;
  uint64_t res;
  if (Abc_AigNodeIsConst(pObj)) {
    res = ~uint64_t(0);
  } else {
    assert(Abc_ObjIsNode(pObj));  // a valid cut bounds the cone
    uint64_t t0 = simulateCone(Abc_ObjFanin0(pObj), cut, memo);
    uint64_t t1 = simulateCone(Abc_ObjFanin1(pObj), cut, memo);
    res = (Abc_ObjFaninC0(pObj) ? ~t0 : t0) & (Abc_ObjFaninC1(pObj) ? ~t1 : t1);
  }
  memo[Abc_ObjId(pObj)] = res;
  return res;
}

static uint64_t coneTruthTable(Abc_Obj_t* pRoot, const Cut& cut) {
  std::unordered_map<int, uint64_t> memo;
  for (int j = 0; j < cut.nLeaves; ++j) {
    int bit = cut.nLeaves - 1 - j;  // leaf j's bit in the input assignment
    uint64_t var = 0;
    for (int p = 0; p < (1 << cut.nLeaves); ++p)
      if ((p >> bit) & 1) var |= uint64_t(1) << p;
    memo[cut.leaves[j]] = var;
  }
  return simulateCone(pRoot, cut, memo) & ttMask(cut.nLeaves);
}

// Enumerate the k-feasible cuts of every node of a strashed AIG, indexed by
// object ID. Unless fKeepDominated is set, a cut is dropped when another cut
// of the same node is a subset of it (i.e. only irredundant cuts are kept).
static std::vector<CutSet> enumerateCuts(Abc_Ntk_t* pNtk, int k,
                                         bool fKeepDominated) {
  std::vector<CutSet> cuts(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t* pObj;
  int i;

  // Constant 1 has the empty cut with function 1.
  Cut cConst;
  cConst.tt = 1;
  cConst.sign = 0;
  cConst.nLeaves = 0;
  cuts[Abc_ObjId(Abc_AigConst1(pNtk))].push_back(cConst);

  Abc_NtkForEachCi(pNtk, pObj, i)
    cuts[Abc_ObjId(pObj)].push_back(makeLeafCut(Abc_ObjId(pObj)));

  Vec_Ptr_t* vNodes = Abc_NtkDfs(pNtk, 0);
  Vec_PtrForEachEntry(Abc_Obj_t*, vNodes, pObj, i) {
    int id = Abc_ObjId(pObj);
    CutSet& cs = cuts[id];
    cs.push_back(makeLeafCut(id));

    const CutSet& cs0 = cuts[Abc_ObjFaninId0(pObj)];
    const CutSet& cs1 = cuts[Abc_ObjFaninId1(pObj)];
    int fC0 = Abc_ObjFaninC0(pObj), fC1 = Abc_ObjFaninC1(pObj);

    for (const Cut& c0 : cs0) {
      for (const Cut& c1 : cs1) {
        Cut m;
        m.sign = c0.sign | c1.sign;
        if (__builtin_popcountll(m.sign) > k) continue;
        if (!mergeLeaves(c0, c1, k, m)) continue;

        bool fSkip = false, fDominates = false;
        for (const Cut& c : cs) {
          if (fKeepDominated ? (c.sign == m.sign && c.nLeaves == m.nLeaves &&
                                isSubset(c, m))
                             : isSubset(c, m)) {
            fSkip = true;  // duplicate, or dominated by an existing cut
            break;
          }
          if (!fKeepDominated && !fDominates && isSubset(m, c))
            fDominates = true;
        }
        if (fSkip) continue;
        if (fDominates)
          cs.erase(std::remove_if(cs.begin(), cs.end(),
                                  [&](const Cut& c) { return isSubset(m, c); }),
                   cs.end());

        if (fKeepDominated) {
          // Merging fanin truth tables is only exact for irredundant cuts.
          m.tt = coneTruthTable(pObj, m);
        } else {
          uint64_t t0 = ttExpand(c0, m), t1 = ttExpand(c1, m);
          if (fC0) t0 = ~t0;
          if (fC1) t1 = ~t1;
          m.tt = t0 & t1 & ttMask(m.nLeaves);
        }
        cs.push_back(m);
      }
    }
  }
  Vec_PtrFree(vNodes);
  return cuts;
}

static void printCutPrefix(int id, const Cut& cut) {
  printf("%d:", id);
  for (int j = 0; j < cut.nLeaves; ++j) printf(" %d", cut.leaves[j]);
  printf(":");
}

// Parses "[-a] [-h] <k>". Returns false (after printing usage) on error.
static bool parseArgs(int argc, char** argv, const char* cmd, const char* what,
                      int& k, bool& fKeepDominated) {
  int c;
  fKeepDominated = false;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "ah")) != EOF) {
    switch (c) {
      case 'a':
        fKeepDominated = true;
        break;
      default:
        goto usage;
    }
  }
  if (argc != globalUtilOptind + 1) goto usage;
  k = atoi(argv[globalUtilOptind]);
  if (k < 1 || k > kMaxCutSize) {
    Abc_Print(-1, "k must be between 1 and %d.\n", kMaxCutSize);
    return false;
  }
  return true;

usage:
  Abc_Print(-2, "usage: %s [-ah] <k>\n", cmd);
  Abc_Print(-2, "\t        prints the %s of every k-feasible cut (1 <= k <= 6)\n", what);
  Abc_Print(-2, "\t-a    : also keep cuts that contain another cut of the node\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return false;
}

static Abc_Ntk_t* getStrashedNtk(Abc_Frame_t* pAbc) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return NULL;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not a strashed AIG. Run \"strash\" first.\n");
    return NULL;
  }
  return pNtk;
}

// -----------------------------------------------------------------------
// lsv_cut_tt (4.1)
// -----------------------------------------------------------------------

int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k;
  bool fKeepDominated;
  if (!parseArgs(argc, argv, "lsv_cut_tt", "truth table", k, fKeepDominated))
    return 1;
  Abc_Ntk_t* pNtk = getStrashedNtk(pAbc);
  if (!pNtk) return 1;

  std::vector<CutSet> cuts = enumerateCuts(pNtk, k, fKeepDominated);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const Cut& cut : cuts[id]) {
      printCutPrefix(id, cut);
      printf(" %llX\n", (unsigned long long)cut.tt);
    }
  }
  return 0;
}

// -----------------------------------------------------------------------
// lsv_cut_bddsize (4.2)
// The ROBDD is built from the cut's truth table by Shannon expansion.
// BDD variable j is leaf j; leaves are sorted by ID, so smaller IDs are
// closer to the root. Returns a referenced node.
// -----------------------------------------------------------------------

static DdNode* ttToBdd(DdManager* dd, uint64_t tt, int nVars, int var) {
  if (nVars == 0) {
    DdNode* r = Cudd_NotCond(Cudd_ReadOne(dd), !(tt & 1));
    Cudd_Ref(r);
    return r;
  }
  // The top variable is the MSB of the input assignment: the upper half of
  // the table is its positive cofactor.
  int half = 1 << (nVars - 1);
  uint64_t lo = tt & ttMask(nVars - 1), hi = tt >> half;
  if (lo == hi) return ttToBdd(dd, lo, nVars - 1, var + 1);

  DdNode* f0 = ttToBdd(dd, lo, nVars - 1, var + 1);
  DdNode* f1 = ttToBdd(dd, hi, nVars - 1, var + 1);
  DdNode* r = Cudd_bddIte(dd, Cudd_bddIthVar(dd, var), f1, f0);
  Cudd_Ref(r);
  Cudd_RecursiveDeref(dd, f0);
  Cudd_RecursiveDeref(dd, f1);
  return r;
}

int Lsv_CommandCutBDDSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k;
  bool fKeepDominated;
  if (!parseArgs(argc, argv, "lsv_cut_bddsize", "ROBDD size", k,
                 fKeepDominated))
    return 1;
  Abc_Ntk_t* pNtk = getStrashedNtk(pAbc);
  if (!pNtk) return 1;

  std::vector<CutSet> cuts = enumerateCuts(pNtk, k, fKeepDominated);
  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const Cut& cut : cuts[id]) {
      DdNode* f = ttToBdd(dd, cut.tt, cut.nLeaves, 0);
      printCutPrefix(id, cut);
      printf(" %d\n", Cudd_DagSize(f));
      Cudd_RecursiveDeref(dd, f);
    }
  }
  Cudd_Quit(dd);
  return 0;
}
