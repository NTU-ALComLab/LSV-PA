#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <cstring>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);
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

typedef std::vector<int> Lsv_Cut_t;

// returns true if a is a subset of b (both sorted)
static bool Lsv_CutIsSubset(const Lsv_Cut_t& a, const Lsv_Cut_t& b) {
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

// adds a cut unless it is dominated; removes existing cuts it dominates
static void Lsv_CutSetAdd(std::vector<Lsv_Cut_t>& cuts, const Lsv_Cut_t& cut) {
  for (size_t i = 0; i < cuts.size(); i++) {
    if (Lsv_CutIsSubset(cuts[i], cut)) return;
  }
  size_t n = 0;
  for (size_t i = 0; i < cuts.size(); i++) {
    if (!Lsv_CutIsSubset(cut, cuts[i])) cuts[n++] = cuts[i];
  }
  cuts.resize(n);
  cuts.push_back(cut);
}

// enumerates all irredundant k-feasible cuts of every object, indexed by ID
static void Lsv_NtkEnumerateCuts(Abc_Ntk_t* pNtk, int k,
                                 std::vector<std::vector<Lsv_Cut_t> >& cuts) {
  Abc_Obj_t* pObj;
  int i;
  cuts.assign(Abc_NtkObjNumMax(pNtk), std::vector<Lsv_Cut_t>());
  Abc_NtkForEachPi(pNtk, pObj, i) {
    cuts[Abc_ObjId(pObj)].push_back(Lsv_Cut_t(1, Abc_ObjId(pObj)));
  }
  // nodes of a strashed AIG are stored in topological order
  Abc_NtkForEachNode(pNtk, pObj, i) {
    std::vector<Lsv_Cut_t>& res = cuts[Abc_ObjId(pObj)];
    const std::vector<Lsv_Cut_t>& cuts0 = cuts[Abc_ObjFaninId0(pObj)];
    const std::vector<Lsv_Cut_t>& cuts1 = cuts[Abc_ObjFaninId1(pObj)];
    res.push_back(Lsv_Cut_t(1, Abc_ObjId(pObj)));
    for (size_t a = 0; a < cuts0.size(); a++) {
      for (size_t b = 0; b < cuts1.size(); b++) {
        Lsv_Cut_t merged;
        std::set_union(cuts0[a].begin(), cuts0[a].end(), cuts1[b].begin(),
                       cuts1[b].end(), std::back_inserter(merged));
        if ((int)merged.size() <= k) Lsv_CutSetAdd(res, merged);
      }
    }
  }
}

// simulates the cone of pObj; leaves are marked with the current trav ID
static word Lsv_NodeSimulate(Abc_Obj_t* pObj, std::vector<word>& sims) {
  if (Abc_NodeIsTravIdCurrent(pObj)) return sims[Abc_ObjId(pObj)];
  Abc_NodeSetTravIdCurrent(pObj);
  word res;
  if (Abc_AigNodeIsConst(pObj)) {
    res = ~(word)0;
  } else {
    assert(Abc_ObjIsNode(pObj));
    word s0 = Lsv_NodeSimulate(Abc_ObjFanin0(pObj), sims);
    word s1 = Lsv_NodeSimulate(Abc_ObjFanin1(pObj), sims);
    if (Abc_ObjFaninC0(pObj)) s0 = ~s0;
    if (Abc_ObjFaninC1(pObj)) s1 = ~s1;
    res = s0 & s1;
  }
  return sims[Abc_ObjId(pObj)] = res;
}

// computes the truth table of pRoot in terms of the cut leaves; the first
// leaf is the most significant bit of the input assignment
static word Lsv_CutTruthTable(Abc_Obj_t* pRoot, const Lsv_Cut_t& cut,
                              std::vector<word>& sims) {
  static const word s_Vars[6] = {
      ABC_CONST(0xAAAAAAAAAAAAAAAA), ABC_CONST(0xCCCCCCCCCCCCCCCC),
      ABC_CONST(0xF0F0F0F0F0F0F0F0), ABC_CONST(0xFF00FF00FF00FF00),
      ABC_CONST(0xFFFF0000FFFF0000), ABC_CONST(0xFFFFFFFF00000000)};
  Abc_Ntk_t* pNtk = Abc_ObjNtk(pRoot);
  int n = (int)cut.size();
  assert(n <= 6);
  Abc_NtkIncrementTravId(pNtk);
  for (int j = 0; j < n; j++) {
    Abc_Obj_t* pLeaf = Abc_NtkObj(pNtk, cut[j]);
    Abc_NodeSetTravIdCurrent(pLeaf);
    sims[cut[j]] = s_Vars[n - 1 - j];
  }
  word tt = Lsv_NodeSimulate(pRoot, sims);
  if (n < 6) tt &= (((word)1) << (1 << n)) - 1;
  return tt;
}

void Lsv_NtkCutTT(Abc_Ntk_t* pNtk, int k) {
  std::vector<std::vector<Lsv_Cut_t> > cuts;
  std::vector<word> sims(Abc_NtkObjNumMax(pNtk), 0);
  Abc_Obj_t* pObj;
  int i;
  Lsv_NtkEnumerateCuts(pNtk, k, cuts);
  Abc_NtkForEachNode(pNtk, pObj, i) {
    const std::vector<Lsv_Cut_t>& nodeCuts = cuts[Abc_ObjId(pObj)];
    for (size_t c = 0; c < nodeCuts.size(); c++) {
      printf("%d:", Abc_ObjId(pObj));
      for (size_t j = 0; j < nodeCuts[c].size(); j++) {
        printf(" %d", nodeCuts[c][j]);
      }
      printf(": %llX\n",
             (unsigned long long)Lsv_CutTruthTable(pObj, nodeCuts[c], sims));
    }
  }
}

// builds the BDD of the cone of pObj; leaves are marked with the current trav
// ID; every node built is referenced and recorded in vVisited
static DdNode* Lsv_NodeBuildBdd(DdManager* dd, Abc_Obj_t* pObj,
                                std::vector<DdNode*>& bdds,
                                std::vector<int>& vVisited) {
  if (Abc_NodeIsTravIdCurrent(pObj)) return bdds[Abc_ObjId(pObj)];
  Abc_NodeSetTravIdCurrent(pObj);
  DdNode* res;
  if (Abc_AigNodeIsConst(pObj)) {
    res = Cudd_ReadOne(dd);
  } else {
    assert(Abc_ObjIsNode(pObj));
    DdNode* bdd0 = Lsv_NodeBuildBdd(dd, Abc_ObjFanin0(pObj), bdds, vVisited);
    DdNode* bdd1 = Lsv_NodeBuildBdd(dd, Abc_ObjFanin1(pObj), bdds, vVisited);
    res = Cudd_bddAnd(dd, Cudd_NotCond(bdd0, Abc_ObjFaninC0(pObj)),
                      Cudd_NotCond(bdd1, Abc_ObjFaninC1(pObj)));
  }
  Cudd_Ref(res);
  vVisited.push_back(Abc_ObjId(pObj));
  return bdds[Abc_ObjId(pObj)] = res;
}

// computes the ROBDD size of pRoot in terms of the cut leaves; leaf j becomes
// BDD variable j, so leaves with smaller IDs are closer to the root
static int Lsv_CutBddSize(DdManager* dd, Abc_Obj_t* pRoot, const Lsv_Cut_t& cut,
                          std::vector<DdNode*>& bdds) {
  Abc_Ntk_t* pNtk = Abc_ObjNtk(pRoot);
  std::vector<int> vVisited;
  Abc_NtkIncrementTravId(pNtk);
  for (size_t j = 0; j < cut.size(); j++) {
    Abc_Obj_t* pLeaf = Abc_NtkObj(pNtk, cut[j]);
    Abc_NodeSetTravIdCurrent(pLeaf);
    bdds[cut[j]] = Cudd_bddIthVar(dd, (int)j);
    Cudd_Ref(bdds[cut[j]]);
    vVisited.push_back(cut[j]);
  }
  int size = Cudd_DagSize(Lsv_NodeBuildBdd(dd, pRoot, bdds, vVisited));
  for (size_t j = 0; j < vVisited.size(); j++) {
    Cudd_RecursiveDeref(dd, bdds[vVisited[j]]);
  }
  return size;
}

void Lsv_NtkCutBddSize(Abc_Ntk_t* pNtk, int k) {
  std::vector<std::vector<Lsv_Cut_t> > cuts;
  std::vector<DdNode*> bdds(Abc_NtkObjNumMax(pNtk), NULL);
  DdManager* dd = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Abc_Obj_t* pObj;
  int i;
  Lsv_NtkEnumerateCuts(pNtk, k, cuts);
  Abc_NtkForEachNode(pNtk, pObj, i) {
    const std::vector<Lsv_Cut_t>& nodeCuts = cuts[Abc_ObjId(pObj)];
    for (size_t c = 0; c < nodeCuts.size(); c++) {
      printf("%d:", Abc_ObjId(pObj));
      for (size_t j = 0; j < nodeCuts[c].size(); j++) {
        printf(" %d", nodeCuts[c][j]);
      }
      printf(": %d\n", Lsv_CutBddSize(dd, pObj, nodeCuts[c], bdds));
    }
  }
  Cudd_Quit(dd);
}

int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k;
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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG (run \"strash\" first).\n");
    return 1;
  }
  if (argc != globalUtilOptind + 1) {
    Abc_Print(-1, "Please specify the cut size.\n");
    return 1;
  }
  k = atoi(argv[globalUtilOptind]);
  if (k < 1 || k > 6) {
    Abc_Print(-1, "Cut size must be between 1 and 6.\n");
    return 1;
  }
  Lsv_NtkCutTT(pNtk, k);
  return 0;

usage:
  Abc_Print( -2, "usage: lsv_cut_tt <k>\n" );
  Abc_Print( -2, "\t        enumerate all k-feasible cuts of every internal AIG node\n" );
  Abc_Print( -2, "\t        and print their truth tables\n" );
  Abc_Print( -2, "\t-h    : print the command usage\n" );
  return 1;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k;
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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG (run \"strash\" first).\n");
    return 1;
  }
  if (argc != globalUtilOptind + 1) {
    Abc_Print(-1, "Please specify the cut size.\n");
    return 1;
  }
  k = atoi(argv[globalUtilOptind]);
  if (k < 1) {
    Abc_Print(-1, "Cut size must be at least 1.\n");
    return 1;
  }
  Lsv_NtkCutBddSize(pNtk, k);
  return 0;

usage:
  Abc_Print( -2, "usage: lsv_cut_bddsize <k>\n" );
  Abc_Print( -2, "\t        enumerate all k-feasible cuts of every internal AIG node\n" );
  Abc_Print( -2, "\t        and print the sizes of their ROBDDs\n" );
  Abc_Print( -2, "\t-h    : print the command usage\n" );
  return 1;
}
