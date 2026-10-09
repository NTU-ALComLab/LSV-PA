#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iterator>
#include <set>
#include <vector>

// ---------------------------------------------------------------------------
// Command registration
// ---------------------------------------------------------------------------
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// ---------------------------------------------------------------------------
// lsv_print_nodes (original example, kept unchanged)
// ---------------------------------------------------------------------------
void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
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

// ---------------------------------------------------------------------------
// Step 1: k-feasible cut enumeration
//
//   cuts(PI)    = { {PI} }
//   cuts(AND n) = { {n} } U { c0 U c1 : c0 in cuts(fanin0),
//                                       c1 in cuts(fanin1), |c0 U c1| <= k }
//
// A cut is a sorted vector of node IDs. In a strashed AIG every node's ID is
// larger than its fanins' IDs, so visiting nodes by increasing ID guarantees
// both fanins' cuts are ready when we reach a node.
// ---------------------------------------------------------------------------
//
// Speed tricks (results are identical without them, just slower):
//  * signature: a 64-bit mask with bit (id % 64) set for every leaf. If
//    popcount(sig0 | sig1) > k, the union surely has > k leaves -> skip
//    without touching the leaves at all.
//  * the merge of two sorted lists stops as soon as it exceeds k leaves.
// ---------------------------------------------------------------------------
typedef std::vector<int> Cut;

static inline uint64_t Lsv_Sig(int id) { return (uint64_t)1 << (id & 63); }

static inline int Lsv_Popcount(uint64_t x) {
  int c = 0;
  for (; x; x &= x - 1) ++c;
  return c;
}

// Merge two sorted cuts into buf; return the size, or -1 if it exceeds k.
static int Lsv_MergeCuts(const Cut& a, const Cut& b, int k, int* buf) {
  size_t i = 0, j = 0;
  int n = 0;
  while (i < a.size() || j < b.size()) {
    int x;
    if (j == b.size() || (i < a.size() && a[i] < b[j])) x = a[i++];
    else if (i == a.size() || b[j] < a[i]) x = b[j++];
    else { x = a[i]; ++i; ++j; }  // same ID in both cuts
    if (n == k) return -1;
    buf[n++] = x;
  }
  return n;
}

static std::vector<std::vector<Cut> > Lsv_EnumerateCuts(Abc_Ntk_t* pNtk, int k) {
  int nObjs = Abc_NtkObjNumMax(pNtk);
  std::vector<std::vector<Cut> > cuts(nObjs);
  std::vector<std::vector<uint64_t> > sigs(nObjs);  // parallel to cuts
  std::vector<int> buf(k);
  Abc_Obj_t* pObj;
  int i;

  // Constant node: needs no leaf (only matters if it is ever used as a fanin).
  int c1 = Abc_ObjId(Abc_AigConst1(pNtk));
  cuts[c1].push_back(Cut());
  sigs[c1].push_back(0);

  Abc_NtkForEachPi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    cuts[id].push_back(Cut(1, id));
    sigs[id].push_back(Lsv_Sig(id));
  }

  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    std::vector<Cut>& myCuts = cuts[id];
    std::vector<uint64_t>& mySigs = sigs[id];
    std::set<Cut> seen;  // drop duplicate cuts

    myCuts.push_back(Cut(1, id));  // trivial cut {n}
    mySigs.push_back(Lsv_Sig(id));
    seen.insert(myCuts.back());

    int f0 = Abc_ObjFaninId0(pObj), f1 = Abc_ObjFaninId1(pObj);
    for (size_t a = 0; a < cuts[f0].size(); ++a) {
      for (size_t b = 0; b < cuts[f1].size(); ++b) {
        uint64_t sig = sigs[f0][a] | sigs[f1][b];
        if (Lsv_Popcount(sig) > k) continue;  // quick reject
        int n = Lsv_MergeCuts(cuts[f0][a], cuts[f1][b], k, &buf[0]);
        if (n < 0) continue;  // more than k leaves
        Cut merged(buf.begin(), buf.begin() + n);
        if (seen.insert(merged).second) {
          myCuts.push_back(merged);
          mySigs.push_back(sig);
        }
      }
    }
  }
  return cuts;
}

static void Lsv_PrintCutPrefix(int rootId, const Cut& cut) {
  printf("%d:", rootId);
  for (size_t i = 0; i < cut.size(); ++i) printf(" %d", cut[i]);
  printf(":");
}

// ---------------------------------------------------------------------------
// Memo table shared by the truth-table and BDD walks.
// Instead of creating a std::map for every cut, we keep one array indexed by
// node ID plus a "stamp": an entry is valid only if stamp[id] == curStamp.
// Starting a new cut just means ++curStamp (O(1) "clear").
// ---------------------------------------------------------------------------
template <typename T>
struct Lsv_Memo {
  std::vector<T> val;
  std::vector<unsigned> stamp;
  unsigned cur;
  explicit Lsv_Memo(int n) : val(n), stamp(n, 0), cur(0) {}
  void newCut() { ++cur; }
  bool has(int id) const { return stamp[id] == cur; }
  void set(int id, T v) { val[id] = v; stamp[id] = cur; }
};

// ---------------------------------------------------------------------------
// Step 2: truth table of a cut
//
// Row index r (0 .. 2^m-1) is an input assignment. The FIRST leaf (smallest
// ID) is the MOST significant bit of r, e.g. for cut "1 2", r = 2 = binary 10
// means node1 = 1, node2 = 0. So leaf p corresponds to bit (m-1-p) of r.
// Bit r of the truth table = function value under assignment r.
//
// Each leaf gets an "elementary" truth table; then we walk the cone from the
// root down to the leaves:  tt(n) = (tt(f0) ^ c0) & (tt(f1) ^ c1).
// ---------------------------------------------------------------------------
static uint64_t Lsv_TtRec(Abc_Obj_t* pObj, Lsv_Memo<uint64_t>& memo,
                          uint64_t mask) {
  int id = Abc_ObjId(pObj);
  if (memo.has(id)) return memo.val[id];  // a leaf, or already computed

  if (Abc_AigNodeIsConst(pObj)) return mask;  // constant 1
  uint64_t t0 = Lsv_TtRec(Abc_ObjFanin0(pObj), memo, mask);
  uint64_t t1 = Lsv_TtRec(Abc_ObjFanin1(pObj), memo, mask);
  if (Abc_ObjFaninC0(pObj)) t0 = ~t0;
  if (Abc_ObjFaninC1(pObj)) t1 = ~t1;
  uint64_t t = t0 & t1 & mask;
  memo.set(id, t);
  return t;
}

static uint64_t Lsv_CutTruthTable(Abc_Obj_t* pRoot, const Cut& cut,
                                  Lsv_Memo<uint64_t>& memo) {
  int m = (int)cut.size();
  int nRows = 1 << m;
  uint64_t mask = (nRows == 64) ? ~(uint64_t)0 : (((uint64_t)1 << nRows) - 1);

  memo.newCut();
  for (int p = 0; p < m; ++p) {
    int bit = m - 1 - p;  // first leaf = MSB of the assignment
    uint64_t tt = 0;
    for (int r = 0; r < nRows; ++r)
      if ((r >> bit) & 1) tt |= (uint64_t)1 << r;
    memo.set(cut[p], tt);
  }
  return Lsv_TtRec(pRoot, memo, mask);
}

// ---------------------------------------------------------------------------
// Step 3: BDD of a cut — same cone walk, but with CUDD operations.
// Leaf p -> BDD variable p. Leaves are sorted by ID and CUDD's default order
// puts variable 0 at the top, so smaller IDs are tested closer to the root.
// Every DdNode we keep is Cudd_Ref'ed (recorded in `owned`) and
// Cudd_RecursiveDeref'ed when the cut is done.
// ---------------------------------------------------------------------------
static DdNode* Lsv_BddRec(DdManager* dd, Abc_Obj_t* pObj,
                          Lsv_Memo<DdNode*>& memo,
                          std::vector<DdNode*>& owned) {
  int id = Abc_ObjId(pObj);
  if (memo.has(id)) return memo.val[id];

  DdNode* f;
  if (Abc_AigNodeIsConst(pObj)) {
    f = Cudd_ReadOne(dd);
  } else {
    DdNode* f0 = Lsv_BddRec(dd, Abc_ObjFanin0(pObj), memo, owned);
    DdNode* f1 = Lsv_BddRec(dd, Abc_ObjFanin1(pObj), memo, owned);
    f = Cudd_bddAnd(dd, Cudd_NotCond(f0, Abc_ObjFaninC0(pObj)),
                    Cudd_NotCond(f1, Abc_ObjFaninC1(pObj)));
  }
  Cudd_Ref(f);
  owned.push_back(f);
  memo.set(id, f);
  return f;
}

static int Lsv_CutBddSize(DdManager* dd, Abc_Obj_t* pRoot, const Cut& cut,
                          Lsv_Memo<DdNode*>& memo) {
  std::vector<DdNode*> owned;
  memo.newCut();
  for (size_t p = 0; p < cut.size(); ++p) {
    DdNode* v = Cudd_bddIthVar(dd, (int)p);
    Cudd_Ref(v);
    owned.push_back(v);
    memo.set(cut[p], v);
  }
  int size = Cudd_DagSize(Lsv_BddRec(dd, pRoot, memo, owned));
  for (size_t i = 0; i < owned.size(); ++i) Cudd_RecursiveDeref(dd, owned[i]);
  return size;
}

// ---------------------------------------------------------------------------
// Command front-ends
// ---------------------------------------------------------------------------
static Abc_Ntk_t* Lsv_GetAigAndK(Abc_Frame_t* pAbc, int argc, char** argv,
                                 int maxK, int* pK) {
  if (argc != 2) return NULL;
  char* end;
  long k = strtol(argv[1], &end, 10);
  if (*end != '\0' || k < 1 || k > maxK) {
    Abc_Print(-1, "k must be an integer between 1 and %d.\n", maxK);
    return NULL;
  }
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return NULL;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Please run \"strash\" first.\n");
    return NULL;
  }
  *pK = (int)k;
  return pNtk;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k;
  Abc_Ntk_t* pNtk = Lsv_GetAigAndK(pAbc, argc, argv, 6, &k);
  if (!pNtk) {
    Abc_Print(-2, "usage: lsv_cut_tt <k>   (1 <= k <= 6)\n");
    return 1;
  }
  std::vector<std::vector<Cut> > cuts = Lsv_EnumerateCuts(pNtk, k);
  Lsv_Memo<uint64_t> memo(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    const std::vector<Cut>& cs = cuts[Abc_ObjId(pObj)];
    for (size_t c = 0; c < cs.size(); ++c) {
      Lsv_PrintCutPrefix(Abc_ObjId(pObj), cs[c]);
      printf(" %llX\n",
             (unsigned long long)Lsv_CutTruthTable(pObj, cs[c], memo));
    }
  }
  return 0;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  int k;
  Abc_Ntk_t* pNtk = Lsv_GetAigAndK(pAbc, argc, argv, 16, &k);
  if (!pNtk) {
    Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
    return 1;
  }
  std::vector<std::vector<Cut> > cuts = Lsv_EnumerateCuts(pNtk, k);
  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Lsv_Memo<DdNode*> memo(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    const std::vector<Cut>& cs = cuts[Abc_ObjId(pObj)];
    for (size_t c = 0; c < cs.size(); ++c) {
      Lsv_PrintCutPrefix(Abc_ObjId(pObj), cs[c]);
      printf(" %d\n", Lsv_CutBddSize(dd, pObj, cs[c], memo));
    }
  }
  Cudd_Quit(dd);
  return 0;
}
