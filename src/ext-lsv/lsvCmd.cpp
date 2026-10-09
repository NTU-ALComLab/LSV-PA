#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/extrab/extraBdd.h" 

#include <cinttypes>
#include <cstdint>
#include <cstdlib>
#include <vector>
#include <algorithm>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPA1CutTT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPA1CutBDDsize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandPA1CutTT, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandPA1CutBDDsize, 0);
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
// PA1 4.1: k-feasible cut enumeration + truth tables
// ---------------------------------------------------------------------------

// A cut is a list of leaf object IDs, kept sorted ascending (at most 6 leaves).
typedef std::vector<int> Lsv_Cut;
typedef std::vector<Lsv_Cut> Lsv_CutSet;

// Truth table of the variable at bit position b of the minterm index.
// Leaf j of an m-leaf cut sits at bit position (m - 1 - j): the first
// (smallest ID) leaf is the MSB of the input assignment.
static const uint64_t s_VarMasks[6] = {
    0xAAAAAAAAAAAAAAAAULL, 0xCCCCCCCCCCCCCCCCULL, 0xF0F0F0F0F0F0F0F0ULL,
    0xFF00FF00FF00FF00ULL, 0xFFFF0000FFFF0000ULL, 0xFFFFFFFF00000000ULL};

// Keeps only the low 2^nVars bits.
static inline uint64_t Lsv_TtMask(int nVars) {
  return nVars == 6 ? ~0ULL : ((1ULL << (1 << nVars)) - 1);
}

// Merges two sorted cuts into pOut (sorted, no duplicate leaves).
// Returns false if the union has more than k leaves.
static bool Lsv_CutMerge(const Lsv_Cut& a, const Lsv_Cut& b, int k,
                         Lsv_Cut& out) {
  // TODO: linear merge of two sorted vectors, bail out once size exceeds k
  int i = 0, j = 0;
  out.clear();
  while (i < a.size() && j < b.size()) {
    if (a[i] < b[j]) {
      out.push_back(a[i]);
      i++;
    } else if (a[i] > b[j]) {
      out.push_back(b[j]);
      j++;
    } else {
      out.push_back(a[i]);
      i++;
      j++;
    }
    if (out.size() > k) return false;
  }
  while (i < a.size()) {
    out.push_back(a[i]);
    i++;
    if (out.size() > k) return false;
  }
  while (j < b.size()) {
    out.push_back(b[j]);
    j++;
    if (out.size() > k) return false;
  }
  return true;  
}

// Adds cut c to the set unless an existing cut is a subset of c (this also
// covers duplicates). Cuts already in the set that are supersets of c are
// removed.
static void Lsv_CutSetAdd(Lsv_CutSet& set, const Lsv_Cut& c) {
  // TODO: dominance check in both directions, then set.push_back(c)
  for (auto it = set.begin(); it != set.end();) {
    const Lsv_Cut& existing = *it;
    // Check if existing cut is a subset of c
    bool existing_subset = std::includes(c.begin(), c.end(), existing.begin(), existing.end());
    // Check if c is a subset of existing cut
    bool c_subset = std::includes(existing.begin(), existing.end(), c.begin(), c.end());
    if (existing_subset) {
      return; // c is dominated by an existing cut
    } else if (c_subset) {
      it = set.erase(it); // remove the dominated existing cut
    } else {
      ++it;
    }
  }
  set.push_back(c);
}

// Fills vCuts[id] for every PI and AND node, in topological (ID) order.
static void Lsv_NtkEnumerateCuts(Abc_Ntk_t* pNtk, int k,
                                 std::vector<Lsv_CutSet>& vCuts) {
  vCuts.assign(Abc_NtkObjNumMax(pNtk), Lsv_CutSet());
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPi(pNtk, pObj, i) {
    vCuts[Abc_ObjId(pObj)].push_back(Lsv_Cut{(int)Abc_ObjId(pObj)});
  }
  Abc_NtkForEachNode(pNtk, pObj, i) {
    Lsv_CutSet& set = vCuts[Abc_ObjId(pObj)];
    set.push_back(Lsv_Cut{(int)Abc_ObjId(pObj)});  // trivial cut
    // TODO: for each a in vCuts[fanin0 ID], b in vCuts[fanin1 ID]:
    //         if Lsv_CutMerge(a, b, k, merged) then Lsv_CutSetAdd(set, merged)
    for (const Lsv_Cut& a : vCuts[Abc_ObjFaninId0(pObj)]) {
      for (const Lsv_Cut& b : vCuts[Abc_ObjFaninId1(pObj)]) {
        Lsv_Cut merged;
        if (Lsv_CutMerge(a, b, k, merged)) Lsv_CutSetAdd(set, merged);
      }
    }
  }
}

// Computes the function of pObj in terms of the leaves' values stored in
// vTt. Leaves are marked with the current traversal ID.
static uint64_t Lsv_CutSimulate_rec(Abc_Obj_t* pObj,
                                    std::vector<uint64_t>& vTt) {
  // TODO: if pObj is marked (leaf or already computed), return vTt[id];
  //       otherwise recurse on both fanins, apply complements
  //       (Abc_ObjFaninC0/C1), AND them, store in vTt[id], mark pObj
  if (Abc_NodeIsTravIdCurrent(pObj)) {
    return vTt[Abc_ObjId(pObj)];
  }
  uint64_t tt0 = Lsv_CutSimulate_rec(Abc_ObjFanin0(pObj), vTt);
  uint64_t tt1 = Lsv_CutSimulate_rec(Abc_ObjFanin1(pObj), vTt);
  if (Abc_ObjFaninC0(pObj)) tt0 = ~tt0;
  if (Abc_ObjFaninC1(pObj)) tt1 = ~tt1;
  vTt[Abc_ObjId(pObj)] = tt0 & tt1;
  Abc_NodeSetTravIdCurrent(pObj);
  return vTt[Abc_ObjId(pObj)];
}

// Truth table of pRoot over the leaves of cut, in the required bit order.
static uint64_t Lsv_CutTruthTable(Abc_Ntk_t* pNtk, Abc_Obj_t* pRoot,
                                  const Lsv_Cut& cut,
                                  std::vector<uint64_t>& vTt) {
  int nVars = cut.size();
  Abc_NtkIncrementTravId(pNtk);
  for (int j = 0; j < nVars; j++) {
    Abc_Obj_t* pLeaf = Abc_NtkObj(pNtk, cut[j]);
    vTt[cut[j]] = s_VarMasks[nVars - 1 - j];
    Abc_NodeSetTravIdCurrent(pLeaf);
  }
  return Lsv_CutSimulate_rec(pRoot, vTt) & Lsv_TtMask(nVars);
}

static void Lsv_NtkCutTT(Abc_Ntk_t* pNtk, int k) {
  std::vector<Lsv_CutSet> vCuts;
  Lsv_NtkEnumerateCuts(pNtk, k, vCuts);

  std::vector<uint64_t> vTt(Abc_NtkObjNumMax(pNtk), 0);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const Lsv_Cut& cut : vCuts[Abc_ObjId(pObj)]) {
      uint64_t tt = Lsv_CutTruthTable(pNtk, pObj, cut, vTt);
      Abc_Print(1, "%d:", Abc_ObjId(pObj));
      for (int leaf : cut) Abc_Print(1, " %d", leaf);
      Abc_Print(1, ": %" PRIX64 "\n", tt);
    }
  }
}

int Lsv_CommandPA1CutTT(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, k;
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
  k = atoi(argv[globalUtilOptind]);
  if (k < 1 || k > 6) {
    Abc_Print(-1, "k must be between 1 and 6.\n");
    return 1;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG (run \"strash\" first).\n");
    return 1;
  }
  Lsv_NtkCutTT(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt [-h] <k>\n");
  Abc_Print(-2, "\t        prints k-feasible cuts and their truth tables\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

// Builds the BDD of pObj in terms of the leaves' BDDs stored in vBddnode.
// Every referenced intermediate BDD is appended to vCreated so the caller
// can release it once the cut is done.
static DdNode* Lsv_CutBDD_rec(Abc_Obj_t* pObj, DdManager* dd,
                             std::vector<DdNode*>& vBddnode,
                             std::vector<DdNode*>& vCreated) {
  if (Abc_NodeIsTravIdCurrent(pObj)) {
    return vBddnode[Abc_ObjId(pObj)];
  }
  DdNode* bdd0 = Lsv_CutBDD_rec(Abc_ObjFanin0(pObj), dd, vBddnode, vCreated);
  DdNode* bdd1 = Lsv_CutBDD_rec(Abc_ObjFanin1(pObj), dd, vBddnode, vCreated);
  bdd0 = Cudd_NotCond(bdd0, Abc_ObjFaninC0(pObj));
  bdd1 = Cudd_NotCond(bdd1, Abc_ObjFaninC1(pObj));
  DdNode* bdd = Cudd_bddAnd(dd, bdd0, bdd1);
  Cudd_Ref(bdd);
  vCreated.push_back(bdd);
  vBddnode[Abc_ObjId(pObj)] = bdd;
  Abc_NodeSetTravIdCurrent(pObj);
  return bdd;
}

static DdNode* Lsv_CutBDD(Abc_Ntk_t*  pNtk, Abc_Obj_t* pRoot, DdManager* dd,
                          const Lsv_Cut& cut,
                          std::vector<DdNode*>& vBddnode,
                          std::vector<DdNode*>& vCreated) {
  int nVars = cut.size();
  Abc_NtkIncrementTravId(pNtk);
  for (int j = 0; j < nVars; j++) {
    Abc_Obj_t* pLeaf = Abc_NtkObj(pNtk, cut[j]);
    vBddnode[cut[j]] = Cudd_bddIthVar(dd, j);
    Abc_NodeSetTravIdCurrent(pLeaf);
  }
  return Lsv_CutBDD_rec(pRoot, dd, vBddnode, vCreated);
}

static void Lsv_NtkCutBDDsize(Abc_Ntk_t* pNtk, int k) {
  std::vector<Lsv_CutSet> vCuts;
  Lsv_NtkEnumerateCuts(pNtk, k, vCuts);

  // One manager shared by all cuts: leaf j of every cut is variable j.
  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, 1 << 12, 0);
  std::vector<DdNode*> vBddnode(Abc_NtkObjNumMax(pNtk), nullptr);
  std::vector<DdNode*> vCreated;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const Lsv_Cut& cut : vCuts[Abc_ObjId(pObj)]) {
      vCreated.clear();
      DdNode* bdd = Lsv_CutBDD(pNtk, pObj, dd, cut, vBddnode, vCreated);
      Abc_Print(1, "%d:", Abc_ObjId(pObj));
      for (int leaf : cut) Abc_Print(1, " %d", leaf);
      Abc_Print(1, ": %d\n", Cudd_DagSize(bdd));
      for (DdNode* n : vCreated) Cudd_RecursiveDeref(dd, n);
    }
  }
  Cudd_Quit(dd);
}

int Lsv_CommandPA1CutBDDsize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, k;
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
  k = atoi(argv[globalUtilOptind]);
  if (k < 1 || k > 6) {
    Abc_Print(-1, "k must be between 1 and 6.\n");
    return 1;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG (run \"strash\" first).\n");
    return 1;
  }
  Lsv_NtkCutBDDsize(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bdd [-h] <k>\n");
  Abc_Print(-2, "\t        prints k-feasible cuts and their BDD sizes\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
