#include <stdint.h>
#include <unordered_map>
#include <vector>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

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

// ---------------------------------------------------------------------------
// k-feasible cuts with truth tables and BDD sizes
//
// The cuts are enumerated bottom-up. The cuts of an AND node are the node
// itself and the unions of one cut of each fanin; a cut is dropped when
// another cut of the same node is a subset of it. Since k <= 6, the function
// of a cut fits in one 64-bit word and is kept with the cut, so the truth
// table of a merged cut is the AND of the two fanin tables after both are
// rewritten over the merged leaves. The BDD is built from the truth table.
//
// Example with leaves {2, 5}: bit 0 of the table is the value for (2,5) =
// (0,0), bit 1 for (0,1), bit 2 for (1,0) and bit 3 for (1,1).
// ---------------------------------------------------------------------------

#define LSV_CUT_MAX 6

// A cut of an AIG node. The truth table is indexed by the leaf values with
// pLeaves[0] as the most significant bit of the index.
struct Lsv_Cut_t {
  int nLeaves;
  int pLeaves[LSV_CUT_MAX];  // sorted in ascending order
  uint64_t uSign;            // bit (Id % 64) is set for every leaf
  uint64_t uTruth;
};

typedef std::vector<Lsv_Cut_t> Lsv_CutVec_t;

static inline uint64_t Lsv_TruthMask(int nVars) {
  return nVars == 6 ? ~(uint64_t)0 : ((uint64_t)1 << (1 << nVars)) - 1;
}

static Lsv_Cut_t Lsv_CutUnit(int Id) {
  Lsv_Cut_t Cut;
  Cut.nLeaves = 1;
  Cut.pLeaves[0] = Id;
  Cut.uSign = (uint64_t)1 << (Id & 63);
  Cut.uTruth = 2;
  return Cut;
}

static inline int Lsv_SignExceeds(uint64_t uSign, int k) {
  int nOnes = 0;
  for (; uSign; uSign &= uSign - 1)
    if (++nOnes > k) return 1;
  return 0;
}

// Returns 1 if all leaves of Small are also leaves of Big.
static int Lsv_CutContains(const Lsv_Cut_t& Big, const Lsv_Cut_t& Small) {
  if (Small.nLeaves > Big.nLeaves || (Small.uSign & ~Big.uSign)) return 0;
  int i = 0;
  for (int j = 0; j < Big.nLeaves && i < Small.nLeaves; ++j) {
    if (Small.pLeaves[i] == Big.pLeaves[j])
      ++i;
    else if (Small.pLeaves[i] < Big.pLeaves[j])
      return 0;
  }
  return i == Small.nLeaves;
}

// Computes the union of the leaves of two cuts. Bit p of *pMask0 (*pMask1) is
// set if the leaf at position p of the result is a leaf of C0 (C1).
// Returns 0 if the union has more than k leaves.
static int Lsv_CutMerge(const Lsv_Cut_t& C0, const Lsv_Cut_t& C1, int k,
                        Lsv_Cut_t& Cut, unsigned* pMask0, unsigned* pMask1) {
  int i = 0, j = 0, n = 0;
  *pMask0 = *pMask1 = 0;
  while (i < C0.nLeaves || j < C1.nLeaves) {
    if (n == k) return 0;
    if (j == C1.nLeaves ||
        (i < C0.nLeaves && C0.pLeaves[i] < C1.pLeaves[j])) {
      *pMask0 |= 1u << n;
      Cut.pLeaves[n++] = C0.pLeaves[i++];
    } else if (i == C0.nLeaves || C1.pLeaves[j] < C0.pLeaves[i]) {
      *pMask1 |= 1u << n;
      Cut.pLeaves[n++] = C1.pLeaves[j++];
    } else {
      *pMask0 |= 1u << n;
      *pMask1 |= 1u << n;
      Cut.pLeaves[n++] = C0.pLeaves[i++];
      ++j;
    }
  }
  Cut.nLeaves = n;
  Cut.uSign = C0.uSign | C1.uSign;
  return 1;
}

// Adds a variable the function does not depend on to a truth table of nVars
// variables. iVar is counted from the least significant variable of the
// index, so every block of 2^iVar bits appears twice in the result.
static uint64_t Lsv_TruthAddVar(uint64_t uTruth, int nVars, int iVar) {
  int nWidth = 1 << iVar;
  uint64_t uBlock = ((uint64_t)1 << nWidth) - 1;
  uint64_t uRes = 0;
  for (int b = (1 << (nVars - iVar)) - 1; b >= 0; --b) {
    uint64_t x = (uTruth >> (b * nWidth)) & uBlock;
    uRes |= (x | (x << nWidth)) << (2 * b * nWidth);
  }
  return uRes;
}

// Rewrites the truth table of a cut with nOld leaves as a truth table over
// the nNew leaves of a larger cut. uMask marks the positions of the old
// leaves in the larger cut. The missing leaves are added from the last
// position to the first, so the leaves behind a new one are already there.
static uint64_t Lsv_TruthExpand(uint64_t uTruth, int nOld, unsigned uMask,
                                int nNew) {
  int nVars = nOld;
  for (int p = nNew - 1; p >= 0 && nVars < nNew; --p)
    if (!((uMask >> p) & 1))
      uTruth = Lsv_TruthAddVar(uTruth, nVars++, nNew - 1 - p);
  return uTruth;
}

// Derives the cuts of an AND node from the cuts of its two fanins.
static void Lsv_NodeCuts(Abc_Obj_t* pObj, int k, const Lsv_CutVec_t& vCuts0,
                         const Lsv_CutVec_t& vCuts1, Lsv_CutVec_t& vCuts) {
  int fCompl0 = Abc_ObjFaninC0(pObj);
  int fCompl1 = Abc_ObjFaninC1(pObj);
  unsigned uMask0, uMask1;
  Lsv_Cut_t Cut;
  vCuts.clear();
  vCuts.push_back(Lsv_CutUnit(Abc_ObjId(pObj)));
  for (size_t a = 0; a < vCuts0.size(); ++a) {
    const Lsv_Cut_t& C0 = vCuts0[a];
    for (size_t b = 0; b < vCuts1.size(); ++b) {
      const Lsv_Cut_t& C1 = vCuts1[b];
      if (Lsv_SignExceeds(C0.uSign | C1.uSign, k)) continue;
      if (!Lsv_CutMerge(C0, C1, k, Cut, &uMask0, &uMask1)) continue;
      // skip the cut if a cut found earlier is a subset of it
      size_t c;
      for (c = 1; c < vCuts.size(); ++c)
        if (Lsv_CutContains(Cut, vCuts[c])) break;
      if (c < vCuts.size()) continue;
      // remove the cuts found earlier that are supersets of it
      size_t w = 1;
      for (c = 1; c < vCuts.size(); ++c)
        if (!Lsv_CutContains(vCuts[c], Cut)) vCuts[w++] = vCuts[c];
      vCuts.resize(w);
      uint64_t t0 = Lsv_TruthExpand(C0.uTruth, C0.nLeaves, uMask0, Cut.nLeaves);
      uint64_t t1 = Lsv_TruthExpand(C1.uTruth, C1.nLeaves, uMask1, Cut.nLeaves);
      if (fCompl0) t0 = ~t0;
      if (fCompl1) t1 = ~t1;
      Cut.uTruth = t0 & t1 & Lsv_TruthMask(Cut.nLeaves);
      vCuts.push_back(Cut);
    }
  }
}

// Builds the BDD of a truth table over variables iVar, ..., nVars - 1,
// where variable iVar is the most significant bit of the index.
static DdNode* Lsv_TruthToBdd_rec(DdManager* dd, uint64_t uTruth, int iVar,
                                  int nVars) {
  int nBits = 1 << (nVars - iVar);
  uint64_t uMask = nBits == 64 ? ~(uint64_t)0 : ((uint64_t)1 << nBits) - 1;
  uTruth &= uMask;
  if (uTruth == 0) return Cudd_ReadLogicZero(dd);
  if (uTruth == uMask) return Cudd_ReadOne(dd);
  int nHalf = nBits >> 1;
  DdNode* bElse = Lsv_TruthToBdd_rec(
      dd, uTruth & (((uint64_t)1 << nHalf) - 1), iVar + 1, nVars);
  Cudd_Ref(bElse);
  DdNode* bThen = Lsv_TruthToBdd_rec(dd, uTruth >> nHalf, iVar + 1, nVars);
  Cudd_Ref(bThen);
  DdNode* bRes = Cudd_bddIte(dd, Cudd_bddIthVar(dd, iVar), bThen, bElse);
  Cudd_Ref(bRes);
  Cudd_RecursiveDeref(dd, bElse);
  Cudd_RecursiveDeref(dd, bThen);
  Cudd_Deref(bRes);
  return bRes;
}

static int Lsv_TruthBddSize(DdManager* dd, uint64_t uTruth, int nVars) {
  DdNode* bFunc = Lsv_TruthToBdd_rec(dd, uTruth, 0, nVars);
  Cudd_Ref(bFunc);
  int nSize = Cudd_DagSize(bFunc);
  Cudd_RecursiveDeref(dd, bFunc);
  return nSize;
}

// Enumerates the k-feasible cuts of every AND node and prints, for each cut,
// its truth table (fBdd = 0) or the size of its BDD (fBdd = 1). If IdOnly is
// not negative, only the cuts of that node are printed.
static void Lsv_NtkPrintCuts(Abc_Ntk_t* pNtk, int k, int fBdd, int IdOnly,
                             int fStats) {
  int nObjs = Abc_NtkObjNumMax(pNtk);
  std::vector<Lsv_CutVec_t> vCuts(nObjs);
  std::vector<int> vRefs(nObjs, 0);
  // BDD sizes already computed: vSizes[number of leaves][truth table]
  std::unordered_map<uint64_t, int> vSizes[LSV_CUT_MAX + 1];
  int pCounts[LSV_CUT_MAX + 1] = {0};
  int nNodes = 0, nCuts = 0, nCutsMax = 0, IdMax = -1;
  abctime clk = Abc_Clock();
  DdManager* dd = NULL;
  Abc_Obj_t* pObj;
  int i;
  if (fBdd) {
    dd = Cudd_Init(LSV_CUT_MAX, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    Cudd_AutodynDisable(dd);
  }
  Abc_NtkForEachObj(pNtk, pObj, i) {
    vRefs[Abc_ObjId(pObj)] = Abc_ObjFanoutNum(pObj);
  }
  Abc_NtkForEachCi(pNtk, pObj, i) {
    vCuts[Abc_ObjId(pObj)].push_back(Lsv_CutUnit(Abc_ObjId(pObj)));
  }
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int Id = Abc_ObjId(pObj);
    int Id0 = Abc_ObjFaninId0(pObj);
    int Id1 = Abc_ObjFaninId1(pObj);
    Lsv_NodeCuts(pObj, k, vCuts[Id0], vCuts[Id1], vCuts[Id]);
    if (IdOnly < 0 || IdOnly == Id) {
      for (size_t c = 0; c < vCuts[Id].size(); ++c) {
        const Lsv_Cut_t& Cut = vCuts[Id][c];
        printf("%d:", Id);
        for (int j = 0; j < Cut.nLeaves; ++j) printf(" %d", Cut.pLeaves[j]);
        if (fBdd) {
          int& nSize = vSizes[Cut.nLeaves][Cut.uTruth];
          if (nSize == 0) nSize = Lsv_TruthBddSize(dd, Cut.uTruth, Cut.nLeaves);
          printf(": %d\n", nSize);
        } else {
          printf(": %llX\n", (unsigned long long)Cut.uTruth);
        }
        pCounts[Cut.nLeaves]++;
      }
      nNodes++;
      nCuts += (int)vCuts[Id].size();
      if (nCutsMax < (int)vCuts[Id].size()) {
        nCutsMax = (int)vCuts[Id].size();
        IdMax = Id;
      }
      if (IdOnly == Id) break;
    }
    // the cuts of a node are no longer needed once all its fanouts are done
    if (--vRefs[Id0] == 0) Lsv_CutVec_t().swap(vCuts[Id0]);
    if (--vRefs[Id1] == 0) Lsv_CutVec_t().swap(vCuts[Id1]);
    if (vRefs[Id] == 0) Lsv_CutVec_t().swap(vCuts[Id]);
  }
  if (fStats) {
    printf("Nodes = %d.  Cuts = %d.  Max cuts per node = %d", nNodes, nCuts,
           nCutsMax);
    if (IdMax >= 0) printf(" (node %d)", IdMax);
    printf(".\nCuts with 1 to %d leaves:", k);
    for (i = 1; i <= k; ++i) printf(" %d", pCounts[i]);
    printf("\n");
    Abc_PrintTime(1, "Time", Abc_Clock() - clk);
  }
  if (dd) Cudd_Quit(dd);
}

static int Lsv_CommandCut(Abc_Frame_t* pAbc, int argc, char** argv, int fBdd) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, k, IdOnly = -1, fStats = 0;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "nsh")) != EOF) {
    switch (c) {
      case 'n':
        if (globalUtilOptind >= argc) {
          Abc_Print(-1, "Switch \"-n\" should be followed by a node ID.\n");
          goto usage;
        }
        IdOnly = atoi(argv[globalUtilOptind]);
        globalUtilOptind++;
        if (IdOnly < 0) goto usage;
        break;
      case 's':
        fStats ^= 1;
        break;
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (argc != globalUtilOptind + 1) goto usage;
  k = atoi(argv[globalUtilOptind]);
  if (k < 1 || k > LSV_CUT_MAX) {
    Abc_Print(-1, "The cut size k should be between 1 and %d.\n", LSV_CUT_MAX);
    return 1;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "This command works only for AIGs (run \"strash\").\n");
    return 1;
  }
  if (IdOnly >= 0 &&
      (IdOnly >= Abc_NtkObjNumMax(pNtk) || !Abc_NtkObj(pNtk, IdOnly) ||
       !Abc_ObjIsNode(Abc_NtkObj(pNtk, IdOnly)))) {
    Abc_Print(-1, "Object %d is not an internal node of the AIG.\n", IdOnly);
    return 1;
  }
  Lsv_NtkPrintCuts(pNtk, k, fBdd, IdOnly, fStats);
  return 0;

usage:
  Abc_Print(-2, "usage: %s [-n <id>] [-sh] <k>\n",
            fBdd ? "lsv_cut_bddsize" : "lsv_cut_tt");
  Abc_Print(-2,
            "\t          prints the %s of the k-feasible cuts of each node\n",
            fBdd ? "BDD sizes" : "truth tables");
  Abc_Print(-2, "\t<k>     : the maximum number of leaves of a cut (1 to %d)\n",
            LSV_CUT_MAX);
  Abc_Print(-2, "\t-n <id> : prints only the cuts of the node with this ID\n");
  Abc_Print(-2, "\t-s      : toggles printing statistics [default = %s]\n",
            fStats ? "yes" : "no");
  Abc_Print(-2, "\t-h      : print the command usage\n");
  return 1;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  return Lsv_CommandCut(pAbc, argc, argv, 0);
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  return Lsv_CommandCut(pAbc, argc, argv, 1);
}
