#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include <vector>

#include "base/abc/abc.h"
#include "bdd/cudd/cudd.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

// The truth table of a k-feasible cut has 2^k bits and is kept in a uint64_t,
// so k cannot exceed 6.
#define LSV_CUT_MAX_K 6

// A cut is its leaf node IDs, sorted ascending so that merging two cuts is a
// plain ordered merge and printing needs no extra sorting. The leaves live in a
// fixed array rather than a vector: a cut never has more than LSV_CUT_MAX_K of
// them, and the enumeration builds tens of millions of these, so one heap
// allocation per cut would dominate the run time. uSign is a cheap superset
// signature -- bit (id % 32) per leaf -- used to reject unequal cuts without
// comparing the leaves.
struct Lsv_Cut_t {
  unsigned uSign;
  int nLeaves;
  int pLeaves[LSV_CUT_MAX_K];
};
typedef std::vector<Lsv_Cut_t> Lsv_CutSet_t;

inline void Lsv_CutSetTrivial(Lsv_Cut_t& c, int id) {
  c.uSign = 1u << (id & 31);
  c.nLeaves = 1;
  c.pLeaves[0] = id;
}

// Ordered merge of two cuts that bails out as soon as the union cannot fit in k
// leaves, so pairs that will be rejected cost almost nothing. Returns false when
// the union is too large.
inline bool Lsv_CutMerge(const Lsv_Cut_t& c0, const Lsv_Cut_t& c1, int k,
                         Lsv_Cut_t& r) {
  unsigned uSign = c0.uSign | c1.uSign;
  int i = 0, j = 0, n = 0;
  // Distinct leaves may collide in the signature, so its population count is a
  // lower bound on the size of the union: too many bits means the merge cannot
  // fit and the loop below can be skipped entirely.
  if (__builtin_popcount(uSign) > k) return false;
  while (i < c0.nLeaves && j < c1.nLeaves) {
    if (n == k) return false;
    if (c0.pLeaves[i] < c1.pLeaves[j])
      r.pLeaves[n++] = c0.pLeaves[i++];
    else if (c0.pLeaves[i] > c1.pLeaves[j])
      r.pLeaves[n++] = c1.pLeaves[j++];
    else
      r.pLeaves[n++] = c0.pLeaves[i++], j++;
  }
  while (i < c0.nLeaves) {
    if (n == k) return false;
    r.pLeaves[n++] = c0.pLeaves[i++];
  }
  while (j < c1.nLeaves) {
    if (n == k) return false;
    r.pLeaves[n++] = c1.pLeaves[j++];
  }
  r.nLeaves = n;
  r.uSign = uSign;  // the union's signature is the OR of the two
  return true;
}

inline bool Lsv_CutSetHas(const Lsv_CutSet_t& v, const Lsv_Cut_t& c) {
  for (size_t i = 0; i < v.size(); ++i)
    if (v[i].uSign == c.uSign && v[i].nLeaves == c.nLeaves &&
        !memcmp(v[i].pLeaves, c.pLeaves, c.nLeaves * sizeof(int)))
      return true;
  return false;
}

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

// Front end shared by the two cut commands: reads the mandatory <k> argument and
// checks that the current network is a strashed AIG. Returns 0 on success; on
// failure the caller is expected to print its own usage message.
int Lsv_CutCommandParse(Abc_Frame_t* pAbc, int argc, char** argv,
                        Abc_Ntk_t** ppNtk, int* pK) {
  Abc_Ntk_t* pNtk;
  int c, k;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        return 1;
      default:
        return 1;
    }
  }
  if (argc != globalUtilOptind + 1) {
    Abc_Print(-1, "Expecting exactly one argument <k>.\n");
    return 1;
  }
  k = atoi(argv[globalUtilOptind]);
  if (k < 2 || k > LSV_CUT_MAX_K) {
    Abc_Print(-1, "The cut size <k> should be between 2 and %d.\n",
              LSV_CUT_MAX_K);
    return 1;
  }
  pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG. Run \"strash\" first.\n");
    return 1;
  }
  *ppNtk = pNtk;
  *pK = k;
  return 0;
}

// Enumerates every k-feasible cut of every node of a strashed AIG. vCuts is
// indexed by node ID (IDs are not contiguous, so it is sized by the object
// count, not the node count). Nodes are visited in increasing ID order, which is
// a topological order because strashing always creates a node after its fanins.
void Lsv_NtkEnumerateCuts(Abc_Ntk_t* pNtk, int k,
                          std::vector<Lsv_CutSet_t>& vCuts) {
  Abc_Obj_t* pObj;
  Lsv_Cut_t Cut;
  int i;
  vCuts.clear();
  vCuts.resize(Abc_NtkObjNumMax(pNtk));

  // A primary input is its own only cut.
  Abc_NtkForEachPi(pNtk, pObj, i) {
    Lsv_CutSetTrivial(Cut, Abc_ObjId(pObj));
    vCuts[Abc_ObjId(pObj)].push_back(Cut);
  }

  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    const Lsv_CutSet_t& vCuts0 = vCuts[Abc_ObjId(Abc_ObjFanin0(pObj))];
    const Lsv_CutSet_t& vCuts1 = vCuts[Abc_ObjId(Abc_ObjFanin1(pObj))];

    // The trivial cut comes first, as in the expected output.
    Lsv_CutSetTrivial(Cut, id);
    vCuts[id].push_back(Cut);

    for (size_t a = 0; a < vCuts0.size(); ++a) {
      for (size_t b = 0; b < vCuts1.size(); ++b) {
        if (!Lsv_CutMerge(vCuts0[a], vCuts1[b], k, Cut)) continue;
        if (Lsv_CutSetHas(vCuts[id], Cut)) continue;
        vCuts[id].push_back(Cut);
      }
    }
  }
}

// Prints "<node id>: <leaf ids>:" -- the part both commands share. The caller
// appends its own truth table or BDD size.
void Lsv_CutPrintPrefix(int nodeId, const Lsv_Cut_t& vCut) {
  printf("%d:", nodeId);
  for (int i = 0; i < vCut.nLeaves; ++i) printf(" %d", vCut.pLeaves[i]);
  printf(":");
}

// Elementary truth tables. Lsv_TtElem[b] is the function "the variable sitting
// at bit b of the input assignment", so bit j of the table is (j >> b) & 1.
static const unsigned long long Lsv_TtElem[LSV_CUT_MAX_K] = {
    0xAAAAAAAAAAAAAAAAull, 0xCCCCCCCCCCCCCCCCull, 0xF0F0F0F0F0F0F0F0ull,
    0xFF00FF00FF00FF00ull, 0xFFFF0000FFFF0000ull, 0xFFFFFFFF00000000ull};

// Scratch state reused across cuts. vTt[id] holds the truth table of node id and
// vStamp[id] records which cut it was computed for, so moving to the next cut is
// a single counter bump instead of clearing the arrays.
struct Lsv_TtMan_t {
  std::vector<unsigned long long> vTt;
  std::vector<unsigned> vStamp;
  unsigned nGen;
  Lsv_TtMan_t(int nObjs) : vTt(nObjs, 0), vStamp(nObjs, 0), nGen(0) {}
};

// Truth table of pObj in terms of the current cut, whose leaves have already been
// stamped with the current generation. A valid cut blocks every path from a
// primary input to the root, so the recursion always stops on a leaf.
unsigned long long Lsv_CutNodeTruth(Abc_Obj_t* pObj, Lsv_TtMan_t& p) {
  int id = Abc_ObjId(pObj);
  unsigned long long t0, t1;
  if (p.vStamp[id] == p.nGen) return p.vTt[id];
  assert(Abc_AigNodeIsAnd(pObj));
  t0 = Lsv_CutNodeTruth(Abc_ObjFanin0(pObj), p);
  t1 = Lsv_CutNodeTruth(Abc_ObjFanin1(pObj), p);
  if (Abc_ObjFaninC0(pObj)) t0 = ~t0;
  if (Abc_ObjFaninC1(pObj)) t1 = ~t1;
  p.vTt[id] = t0 & t1;
  p.vStamp[id] = p.nGen;
  return p.vTt[id];
}

// Truth table of one cut. The first leaf is the most significant variable of the
// input assignment, so leaf i takes the elementary table of bit (m-1-i).
unsigned long long Lsv_CutTruth(Abc_Obj_t* pRoot, const Lsv_Cut_t& vCut,
                                Lsv_TtMan_t& p) {
  int i, m = vCut.nLeaves;
  unsigned long long tt;
  ++p.nGen;
  for (i = 0; i < m; ++i) {
    p.vTt[vCut.pLeaves[i]] = Lsv_TtElem[m - 1 - i];
    p.vStamp[vCut.pLeaves[i]] = p.nGen;
  }
  tt = Lsv_CutNodeTruth(pRoot, p);
  // Only the low 2^m bits are meaningful. Shifting by 64 is undefined, so the
  // full-width case is left alone.
  if (m < LSV_CUT_MAX_K) tt &= (1ull << (1 << m)) - 1;
  return tt;
}

void Lsv_NtkPrintCutTruth(Abc_Ntk_t* pNtk, int k) {
  std::vector<Lsv_CutSet_t> vCuts;
  Lsv_TtMan_t tt(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t* pObj;
  int i;
  Lsv_NtkEnumerateCuts(pNtk, k, vCuts);
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (size_t c = 0; c < vCuts[id].size(); ++c) {
      Lsv_CutPrintPrefix(id, vCuts[id][c]);
      printf(" %llX\n", Lsv_CutTruth(pObj, vCuts[id][c], tt));
    }
  }
}

// CUDD state reused across cuts. The manager is created with exactly k
// variables and dynamic reordering left off, so variable i stays at level i:
// leaf i of a cut is the i-th smallest node ID, which is what the assignment
// means by "smaller node IDs must be tested earlier".
struct Lsv_BddMan_t {
  DdManager* dd;
  std::vector<DdNode*> vBdd;
  std::vector<unsigned> vStamp;
  std::vector<int> vTouched;  // ids referenced during the current cut
  unsigned nGen;
  Lsv_BddMan_t(int nObjs, int k)
      : dd(Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0)),
        vBdd(nObjs, (DdNode*)NULL),
        vStamp(nObjs, 0),
        nGen(0) {}
  ~Lsv_BddMan_t() { Cudd_Quit(dd); }
};

// BDD of pObj in terms of the current cut, whose leaves have already been bound
// to BDD variables. Every node built here is referenced and recorded so that the
// whole cut can be dereferenced in one sweep afterwards.
DdNode* Lsv_CutNodeBdd(Abc_Obj_t* pObj, Lsv_BddMan_t& p) {
  // Note: b0/b1/a0/a1/z0/z1 are macros in bdd/extrab/extraBdd.h, so the locals
  // here have to be spelled out.
  int id = Abc_ObjId(pObj);
  DdNode *bFanin0, *bFanin1, *bNode;
  if (p.vStamp[id] == p.nGen) return p.vBdd[id];
  assert(Abc_AigNodeIsAnd(pObj));
  bFanin0 = Lsv_CutNodeBdd(Abc_ObjFanin0(pObj), p);
  bFanin1 = Lsv_CutNodeBdd(Abc_ObjFanin1(pObj), p);
  if (Abc_ObjFaninC0(pObj)) bFanin0 = Cudd_Not(bFanin0);
  if (Abc_ObjFaninC1(pObj)) bFanin1 = Cudd_Not(bFanin1);
  bNode = Cudd_bddAnd(p.dd, bFanin0, bFanin1);
  Cudd_Ref(bNode);
  p.vBdd[id] = bNode;
  p.vStamp[id] = p.nGen;
  p.vTouched.push_back(id);
  return bNode;
}

// ROBDD size of one cut, as reported by Cudd_DagSize (decision nodes plus the
// terminal). Leaf i takes BDD variable i, so the cut's smallest node ID ends up
// closest to the root.
int Lsv_CutBddSize(Abc_Obj_t* pRoot, const Lsv_Cut_t& vCut, Lsv_BddMan_t& p) {
  int i, m = vCut.nLeaves, nSize;
  DdNode* bVar;
  ++p.nGen;
  p.vTouched.clear();
  for (i = 0; i < m; ++i) {
    bVar = Cudd_bddIthVar(p.dd, i);
    Cudd_Ref(bVar);
    p.vBdd[vCut.pLeaves[i]] = bVar;
    p.vStamp[vCut.pLeaves[i]] = p.nGen;
    p.vTouched.push_back(vCut.pLeaves[i]);
  }
  nSize = Cudd_DagSize(Lsv_CutNodeBdd(pRoot, p));
  for (i = 0; i < (int)p.vTouched.size(); ++i)
    Cudd_RecursiveDeref(p.dd, p.vBdd[p.vTouched[i]]);
  return nSize;
}

void Lsv_NtkPrintCutBddSize(Abc_Ntk_t* pNtk, int k) {
  std::vector<Lsv_CutSet_t> vCuts;
  Lsv_BddMan_t bdd(Abc_NtkObjNumMax(pNtk), k);
  Abc_Obj_t* pObj;
  int i;
  Lsv_NtkEnumerateCuts(pNtk, k, vCuts);
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (size_t c = 0; c < vCuts[id].size(); ++c) {
      Lsv_CutPrintPrefix(id, vCuts[id][c]);
      printf(" %d\n", Lsv_CutBddSize(pObj, vCuts[id][c], bdd));
    }
  }
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk;
  int k;
  if (Lsv_CutCommandParse(pAbc, argc, argv, &pNtk, &k)) goto usage;
  Lsv_NtkPrintCutTruth(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
  Abc_Print(-2,
            "\t        prints the truth table of every k-feasible cut of every"
            " node in the AIG\n");
  Abc_Print(-2, "\t<k>   : the cut size, between 2 and %d\n", LSV_CUT_MAX_K);
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk;
  int k;
  if (Lsv_CutCommandParse(pAbc, argc, argv, &pNtk, &k)) goto usage;
  Lsv_NtkPrintCutBddSize(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
  Abc_Print(-2,
            "\t        prints the ROBDD size of every k-feasible cut of every"
            " node in the AIG\n");
  Abc_Print(-2, "\t<k>   : the cut size, between 2 and %d\n", LSV_CUT_MAX_K);
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
