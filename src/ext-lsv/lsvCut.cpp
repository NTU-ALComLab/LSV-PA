#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

// Truth tables of up to 6 inputs fit in one 64-bit word.
static const int LSV_CUT_MAX_LEAVES = 6;

// A cut is a set of leaf node IDs kept in ascending order.  The signature has
// bit (id % 64) set for every leaf: if a's signature has a bit that b's lacks,
// a cannot be a subset of b, which skips most leaf-by-leaf comparisons.
struct Lsv_Cut_t {
  int nLeaves;
  int pLeaves[LSV_CUT_MAX_LEAVES];
  uint64_t uSign;
};

static Lsv_Cut_t Lsv_CutTrivial(int id) {
  Lsv_Cut_t cut;
  cut.nLeaves = 1;
  cut.pLeaves[0] = id;
  cut.uSign = 1ULL << (id % 64);
  return cut;
}

// Stores the union of a and b in pOut; fails if it has more than k leaves.
static bool Lsv_CutMerge(const Lsv_Cut_t& a, const Lsv_Cut_t& b, int k,
                         Lsv_Cut_t* pOut) {
  // Distinct signature bits come from distinct leaves, so this never rejects a
  // union that fits.
  if (__builtin_popcountll(a.uSign | b.uSign) > k) return false;
  int i = 0, j = 0, n = 0;
  while (i < a.nLeaves || j < b.nLeaves) {
    int id;
    if (j == b.nLeaves || (i < a.nLeaves && a.pLeaves[i] < b.pLeaves[j]))
      id = a.pLeaves[i++];
    else if (i == a.nLeaves || b.pLeaves[j] < a.pLeaves[i])
      id = b.pLeaves[j++];
    else
      id = a.pLeaves[i++], j++;
    if (n == k) return false;
    pOut->pLeaves[n++] = id;
  }
  pOut->nLeaves = n;
  pOut->uSign = a.uSign | b.uSign;
  return true;
}

// Returns true if every leaf of a is also a leaf of b.
static bool Lsv_CutIsSubset(const Lsv_Cut_t& a, const Lsv_Cut_t& b) {
  if (a.nLeaves > b.nLeaves || (a.uSign & ~b.uSign)) return false;
  int j = 0;
  for (int i = 0; i < a.nLeaves; i++) {
    while (j < b.nLeaves && b.pLeaves[j] < a.pLeaves[i]) j++;
    if (j == b.nLeaves || b.pLeaves[j] != a.pLeaves[i]) return false;
    j++;
  }
  return true;
}

// Adds cut to vCuts unless it duplicates or is dominated by (is a superset of)
// a cut already there, and drops the cuts that it dominates.
static void Lsv_CutSetAdd(std::vector<Lsv_Cut_t>& vCuts, const Lsv_Cut_t& cut) {
  for (const Lsv_Cut_t& old : vCuts)
    if (Lsv_CutIsSubset(old, cut)) return;
  size_t nKept = 0;
  for (size_t i = 0; i < vCuts.size(); i++)
    if (!Lsv_CutIsSubset(cut, vCuts[i])) vCuts[nKept++] = vCuts[i];
  vCuts.resize(nKept);
  vCuts.push_back(cut);
}

// Computes the non-dominated k-feasible cuts of pObj into vCuts[id], after
// those of its fanins.  A CI has only its trivial cut.  An AND node has its
// trivial cut plus every union of a fanin-0 cut and a fanin-1 cut that fits in
// k leaves; merging only non-dominated fanin cuts still reaches every
// non-dominated cut of the node.
static void Lsv_ObjComputeCuts(Abc_Obj_t* pObj, int k,
                               std::vector<std::vector<Lsv_Cut_t>>& vCuts) {
  int id = Abc_ObjId(pObj);
  if (!vCuts[id].empty()) return;
  if (!Abc_AigNodeIsAnd(pObj)) {
    vCuts[id].push_back(Lsv_CutTrivial(id));
    return;
  }
  Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pObj);
  Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pObj);
  Lsv_ObjComputeCuts(pFanin0, k, vCuts);
  Lsv_ObjComputeCuts(pFanin1, k, vCuts);
  std::vector<Lsv_Cut_t>& vNodeCuts = vCuts[id];
  vNodeCuts.push_back(Lsv_CutTrivial(id));
  Lsv_Cut_t merged;
  for (const Lsv_Cut_t& cut0 : vCuts[Abc_ObjId(pFanin0)])
    for (const Lsv_Cut_t& cut1 : vCuts[Abc_ObjId(pFanin1)])
      if (Lsv_CutMerge(cut0, cut1, k, &merged)) Lsv_CutSetAdd(vNodeCuts, merged);
}

// Truth table of the input at bit position p of the assignment index, i.e.
// bit m is set iff bit p of m is 1.
static const uint64_t s_VarTruths[LSV_CUT_MAX_LEAVES] = {
    0xAAAAAAAAAAAAAAAAULL, 0xCCCCCCCCCCCCCCCCULL, 0xF0F0F0F0F0F0F0F0ULL,
    0xFF00FF00FF00FF00ULL, 0xFFFF0000FFFF0000ULL, 0xFFFFFFFF00000000ULL};

// Scratch space for simulating one cone at a time.  vValues[id] is valid only
// while vStamps[id] == stamp, so a new cone starts by bumping the stamp.
struct Lsv_Sim_t {
  std::vector<unsigned> vStamps;
  std::vector<uint64_t> vValues;
  unsigned stamp;
};

static uint64_t Lsv_ObjSimulate(Abc_Obj_t* pObj, Lsv_Sim_t& sim) {
  int id = Abc_ObjId(pObj);
  if (sim.vStamps[id] == sim.stamp) return sim.vValues[id];
  // Every path from a CI to the root passes through a leaf, so everything
  // reached before a leaf is an AND node inside the cone.
  assert(Abc_AigNodeIsAnd(pObj));
  uint64_t value0 = Lsv_ObjSimulate(Abc_ObjFanin0(pObj), sim);
  uint64_t value1 = Lsv_ObjSimulate(Abc_ObjFanin1(pObj), sim);
  if (Abc_ObjFaninC0(pObj)) value0 = ~value0;
  if (Abc_ObjFaninC1(pObj)) value1 = ~value1;
  sim.vStamps[id] = sim.stamp;
  return sim.vValues[id] = value0 & value1;
}

// Truth table of pRoot over the leaves of cut.  The i-th leaf in ascending ID
// order is bit (nLeaves - 1 - i) of the assignment index, so the smallest ID is
// the most significant input; bit m of the result is the output for
// assignment m.
static uint64_t Lsv_CutComputeTruth(Abc_Obj_t* pRoot, const Lsv_Cut_t& cut,
                                    Lsv_Sim_t& sim) {
  sim.stamp++;
  for (int i = 0; i < cut.nLeaves; i++) {
    int id = cut.pLeaves[i];
    sim.vStamps[id] = sim.stamp;
    sim.vValues[id] = s_VarTruths[cut.nLeaves - 1 - i];
  }
  uint64_t truth = Lsv_ObjSimulate(pRoot, sim);
  int nBits = 1 << cut.nLeaves;
  return nBits == 64 ? truth : truth & ((1ULL << nBits) - 1);
}

// Builds the BDD of a cone over the leaves of one cut at a time.  Leaf i of
// the cut (ascending ID order) is variable i, and the manager never reorders,
// so variable i stays at level i: smaller IDs are tested closer to the root.
// vNodes[id] is valid only while vStamps[id] == stamp; vBuilt lists the AND
// nodes whose BDDs this cone referenced, so they can be released afterwards.
struct Lsv_BddBuilder_t {
  DdManager* dd;
  std::vector<unsigned> vStamps;
  std::vector<DdNode*> vNodes;
  std::vector<int> vBuilt;
  unsigned stamp;
};

static DdNode* Lsv_ObjBuildBdd(Abc_Obj_t* pObj, Lsv_BddBuilder_t& bld) {
  int id = Abc_ObjId(pObj);
  if (bld.vStamps[id] == bld.stamp) return bld.vNodes[id];
  // As in Lsv_ObjSimulate, only AND nodes inside the cone get here.
  assert(Abc_AigNodeIsAnd(pObj));
  DdNode* bFanin0 = Cudd_NotCond(Lsv_ObjBuildBdd(Abc_ObjFanin0(pObj), bld),
                                 Abc_ObjFaninC0(pObj));
  DdNode* bFanin1 = Cudd_NotCond(Lsv_ObjBuildBdd(Abc_ObjFanin1(pObj), bld),
                                 Abc_ObjFaninC1(pObj));
  DdNode* bNode = Cudd_bddAnd(bld.dd, bFanin0, bFanin1);
  assert(bNode != NULL);
  Cudd_Ref(bNode);
  bld.vStamps[id] = bld.stamp;
  bld.vBuilt.push_back(id);
  return bld.vNodes[id] = bNode;
}

// Number of nodes, including the constant node, in the BDD of pRoot over the
// leaves of cut.
static int Lsv_CutComputeBddSize(Abc_Obj_t* pRoot, const Lsv_Cut_t& cut,
                                 Lsv_BddBuilder_t& bld) {
  bld.stamp++;
  for (int i = 0; i < cut.nLeaves; i++) {
    int id = cut.pLeaves[i];
    bld.vStamps[id] = bld.stamp;
    bld.vNodes[id] = Cudd_bddIthVar(bld.dd, i);
  }
  int size = Cudd_DagSize(Lsv_ObjBuildBdd(pRoot, bld));
  for (int id : bld.vBuilt) Cudd_RecursiveDeref(bld.dd, bld.vNodes[id]);
  bld.vBuilt.clear();
  return size;
}

// Prints "<node>: <leaves>: " followed by printValue(pNode, cut) for every
// k-feasible cut of every AND node, in ascending node ID order.
template <typename PrintValue>
static void Lsv_NtkPrintCuts(Abc_Ntk_t* pNtk, int k, PrintValue printValue) {
  std::vector<std::vector<Lsv_Cut_t>> vCuts(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    if (!Abc_AigNodeIsAnd(pObj)) continue;  // the constant-1 node
    Lsv_ObjComputeCuts(pObj, k, vCuts);
    for (const Lsv_Cut_t& cut : vCuts[Abc_ObjId(pObj)]) {
      printf("%d:", Abc_ObjId(pObj));
      for (int j = 0; j < cut.nLeaves; j++) printf(" %d", cut.pLeaves[j]);
      printf(": ");
      printValue(pObj, cut);
      printf("\n");
    }
  }
}

// Parses "<pCommand> [-h] <k>" and fetches the current network, which must be
// an AIG.  Returns false after printing an error or the usage.
static bool Lsv_CutCommandParse(Abc_Frame_t* pAbc, int argc, char** argv,
                                const char* pCommand, const char* pWhat,
                                Abc_Ntk_t** ppNtk, int* pK) {
  char* pEnd;
  long k;
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
  k = strtol(argv[globalUtilOptind], &pEnd, 10);
  if (*pEnd != '\0' || k < 1 || k > LSV_CUT_MAX_LEAVES) {
    Abc_Print(-1, "k must be an integer from 1 to %d.\n", LSV_CUT_MAX_LEAVES);
    return false;
  }
  *ppNtk = Abc_FrameReadNtk(pAbc);
  if (!*ppNtk) {
    Abc_Print(-1, "Empty network.\n");
    return false;
  }
  if (!Abc_NtkIsStrash(*ppNtk)) {
    Abc_Print(-1, "The network is not an AIG; run \"strash\" first.\n");
    return false;
  }
  *pK = (int)k;
  return true;

usage:
  Abc_Print(-2, "usage: %s [-h] <k>\n", pCommand);
  Abc_Print(-2, "\t        prints the %s of every k-feasible cut of every AND node\n", pWhat);
  Abc_Print(-2, "\t<k>   : max number of cut leaves, from 1 to %d\n", LSV_CUT_MAX_LEAVES);
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return false;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk;
  int k;
  if (!Lsv_CutCommandParse(pAbc, argc, argv, "lsv_cut_tt", "truth table",
                           &pNtk, &k))
    return 1;
  Lsv_Sim_t sim;
  sim.vStamps.assign(Abc_NtkObjNumMax(pNtk), 0);
  sim.vValues.resize(Abc_NtkObjNumMax(pNtk));
  sim.stamp = 0;
  Lsv_NtkPrintCuts(pNtk, k, [&](Abc_Obj_t* pRoot, const Lsv_Cut_t& cut) {
    printf("%llX", (unsigned long long)Lsv_CutComputeTruth(pRoot, cut, sim));
  });
  return 0;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk;
  int k;
  if (!Lsv_CutCommandParse(pAbc, argc, argv, "lsv_cut_bddsize", "BDD size",
                           &pNtk, &k))
    return 1;
  Lsv_BddBuilder_t bld;
  bld.dd = Cudd_Init(LSV_CUT_MAX_LEAVES, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Cudd_AutodynDisable(bld.dd);  // the variable order must stay by node ID
  bld.vStamps.assign(Abc_NtkObjNumMax(pNtk), 0);
  bld.vNodes.resize(Abc_NtkObjNumMax(pNtk));
  bld.stamp = 0;
  Lsv_NtkPrintCuts(pNtk, k, [&](Abc_Obj_t* pRoot, const Lsv_Cut_t& cut) {
    printf("%d", Lsv_CutComputeBddSize(pRoot, cut, bld));
  });
  Cudd_Quit(bld.dd);
  return 0;
}
