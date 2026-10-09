#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <cstdint>
#include <map>
#include <vector>

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

typedef std::vector<int> Cut;      // leaf IDs of one cut, ascending
typedef std::vector<Cut> CutList;  // all cuts of one node

// Is node x a leaf of the cut?
static bool Lsv_CutHas(const Cut& cut, int x) {
  for (int leaf : cut)
    if (leaf == x) return true;
  return false;
}

// Is every leaf of a also a leaf of b?
static bool Lsv_CutIsSubset(const Cut& a, const Cut& b) {
  for (int leaf : a)
    if (!Lsv_CutHas(b, leaf)) return false;
  return true;
}

// Store the union of a and b in c, ascending.
static void Lsv_CutUnion(const Cut& a, const Cut& b, Cut& c) {
  c = a;
  for (int leaf : b)
    if (!Lsv_CutHas(a, leaf)) c.push_back(leaf);
  std::sort(c.begin(), c.end());
}

// Add cut c to the list so that no cut in the list contains another.
static void Lsv_CutAdd(CutList& cuts, const Cut& c) {
  // skip c if it contains (or equals) a cut already in the list
  for (const Cut& old : cuts)
    if (Lsv_CutIsSubset(old, c)) return;
  // remove the cuts that contain c
  for (int i = cuts.size() - 1; i >= 0; i--)
    if (Lsv_CutIsSubset(c, cuts[i])) cuts.erase(cuts.begin() + i);
  cuts.push_back(c);
}

// Cuts with at most k leaves for every input and AND node, indexed by ID.
static std::vector<CutList> Lsv_NtkEnumCuts(Abc_Ntk_t* pNtk, int k) {
  std::vector<CutList> cuts(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t* pObj;
  int i;
  // an input has one cut: itself
  Abc_NtkForEachCi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    cuts[id].push_back({id});
  }
  // AND nodes are visited in ID order, so both fanins are done first
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    cuts[id].push_back({id});
    Cut c;
    for (const Cut& c0 : cuts[Abc_ObjFaninId0(pObj)]) {
      for (const Cut& c1 : cuts[Abc_ObjFaninId1(pObj)]) {
        Lsv_CutUnion(c0, c1, c);
        if ((int)c.size() <= k) Lsv_CutAdd(cuts[id], c);
      }
    }
  }
  return cuts;
}

// Truth table of the input that is bit p of the row number.
static const uint64_t Lsv_VarTruth[6] = {
    0xAAAAAAAAAAAAAAAA, 0xCCCCCCCCCCCCCCCC, 0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00, 0xFFFF0000FFFF0000, 0xFFFFFFFF00000000};

// Truth table of a node; tt already holds the cut leaves.
static uint64_t Lsv_CutTruth_rec(Abc_Obj_t* pObj,
                                 std::map<int, uint64_t>& tt) {
  int id = Abc_ObjId(pObj);
  if (tt.count(id)) return tt[id];
  uint64_t t0 = Lsv_CutTruth_rec(Abc_ObjFanin0(pObj), tt);
  uint64_t t1 = Lsv_CutTruth_rec(Abc_ObjFanin1(pObj), tt);
  if (Abc_ObjFaninC0(pObj)) t0 = ~t0;
  if (Abc_ObjFaninC1(pObj)) t1 = ~t1;
  tt[id] = t0 & t1;
  return tt[id];
}

// Truth table of pRoot in terms of the cut leaves.
static uint64_t Lsv_CutTruth(Abc_Obj_t* pRoot, const Cut& cut) {
  int n = cut.size();
  std::map<int, uint64_t> tt;
  // the first leaf is the highest bit of the row number
  for (int i = 0; i < n; i++) tt[cut[i]] = Lsv_VarTruth[n - 1 - i];
  uint64_t truth = Lsv_CutTruth_rec(pRoot, tt);
  // keep only the 2^n rows that are used
  int nRows = 1 << n;
  if (nRows < 64) truth &= (1ULL << nRows) - 1;
  return truth;
}

// BDD of a node; bdd already holds the cut leaves.
static DdNode* Lsv_CutBdd_rec(DdManager* dd, Abc_Obj_t* pObj,
                              std::map<int, DdNode*>& bdd) {
  int id = Abc_ObjId(pObj);
  if (bdd.count(id)) return bdd[id];
  DdNode* bdd0 = Lsv_CutBdd_rec(dd, Abc_ObjFanin0(pObj), bdd);
  DdNode* bdd1 = Lsv_CutBdd_rec(dd, Abc_ObjFanin1(pObj), bdd);
  if (Abc_ObjFaninC0(pObj)) bdd0 = Cudd_Not(bdd0);
  if (Abc_ObjFaninC1(pObj)) bdd1 = Cudd_Not(bdd1);
  bdd[id] = Cudd_bddAnd(dd, bdd0, bdd1);
  Cudd_Ref(bdd[id]);
  return bdd[id];
}

// Number of BDD nodes of pRoot in terms of the cut leaves.
static int Lsv_CutBddSize(DdManager* dd, Abc_Obj_t* pRoot, const Cut& cut) {
  int n = cut.size();
  std::map<int, DdNode*> bdd;
  // leaf i is BDD variable i, so a smaller ID is closer to the BDD root
  for (int i = 0; i < n; i++) {
    bdd[cut[i]] = Cudd_bddIthVar(dd, i);
    Cudd_Ref(bdd[cut[i]]);
  }
  int size = Cudd_DagSize(Lsv_CutBdd_rec(dd, pRoot, bdd));
  // release every BDD that was built
  for (auto& entry : bdd) Cudd_RecursiveDeref(dd, entry.second);
  return size;
}

// Print "<node>: <cut>: <truth table or BDD size>" for every AND node.
static void Lsv_NtkPrintCuts(Abc_Ntk_t* pNtk, int k, int fBdd) {
  std::vector<CutList> cuts = Lsv_NtkEnumCuts(pNtk, k);
  // k BDD variables in the fixed order 0, 1, ..., k-1
  DdManager* dd = NULL;
  if (fBdd) dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const Cut& cut : cuts[Abc_ObjId(pObj)]) {
      printf("%d:", Abc_ObjId(pObj));
      for (int leaf : cut) printf(" %d", leaf);
      if (fBdd)
        printf(": %d\n", Lsv_CutBddSize(dd, pObj, cut));
      else
        printf(": %llX\n", (unsigned long long)Lsv_CutTruth(pObj, cut));
    }
  }
  if (fBdd) Cudd_Quit(dd);
}

// Shared by both commands: fBdd = 0 prints truth tables, 1 prints BDD sizes.
static int Lsv_CommandCut(Abc_Frame_t* pAbc, int argc, char** argv, int fBdd) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int k = 0;
  if (argc == 2) k = atoi(argv[1]);
  if (k < 1 || k > 6) {
    Abc_Print(-2, "usage: %s <k>\n", argv[0]);
    Abc_Print(-2, "\t<k> : the maximum number of leaves in a cut (1 to 6)\n");
    return 1;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "This command works only on AIGs (run \"strash\" first).\n");
    return 1;
  }
  Lsv_NtkPrintCuts(pNtk, k, fBdd);
  return 0;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  return Lsv_CommandCut(pAbc, argc, argv, 0);
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  return Lsv_CommandCut(pAbc, argc, argv, 1);
}
