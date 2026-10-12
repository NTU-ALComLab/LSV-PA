#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <unordered_map>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddsize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddsize, 0);
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

struct Lsv_Cut {
  int cut_nodes[6];
  int cut_size;  // number of leaves in the cut (<= 6)
  uint64_t truth_table;
};

// Returns a mask with 2^nVars bits set to 1, or all bits set if nVars >= 6.
static uint64_t Lsv_TtMask(int cut_size) {
  return cut_size >= 6 ? ~(uint64_t)0 : (((uint64_t)1 << (1 << cut_size)) - 1);
}

static Lsv_Cut Lsv_CutTrivial(int id) {
  Lsv_Cut cut;
  cut.cut_nodes[0] = id;
  cut.cut_size = 1;
  cut.truth_table = 0x2;
  return cut;
}

static bool Lsv_CutMerge(const Lsv_Cut& c0, const Lsv_Cut& c1, int k, Lsv_Cut& cut) {
  int p = 0, q = 0, n = 0;
  while (p < c0.cut_size || q < c1.cut_size) {
    if (n == k) return false;
    if (q == c1.cut_size || (p < c0.cut_size && c0.cut_nodes[p] < c1.cut_nodes[q]))
      cut.cut_nodes[n++] = c0.cut_nodes[p++];
    else if (p == c0.cut_size || c1.cut_nodes[q] < c0.cut_nodes[p])
      cut.cut_nodes[n++] = c1.cut_nodes[q++];
    else
      cut.cut_nodes[n++] = c0.cut_nodes[p++], q++;
  }
  cut.cut_size = n;
  return true;
}

static bool Lsv_CutIsEqual(const Lsv_Cut& a, const Lsv_Cut& b) {
  if (a.cut_size != b.cut_size) return false;
  for (int p = 0; p < a.cut_size; p++) {
    if (a.cut_nodes[p] != b.cut_nodes[p]) return false;
  }
  return true;
}

static void Lsv_CutAdd(std::vector<Lsv_Cut>& cuts, const Lsv_Cut& cut) {
  for (const Lsv_Cut& e : cuts) {
    if (Lsv_CutIsEqual(e, cut)) return;
  }
  cuts.push_back(cut);
}

// Truth table of the variable that is bit b of the minterm index.
static const uint64_t s_VarTt[6] = {
    0xAAAAAAAAAAAAAAAAull, 0xCCCCCCCCCCCCCCCCull, 0xF0F0F0F0F0F0F0F0ull,
    0xFF00FF00FF00FF00ull, 0xFFFF0000FFFF0000ull, 0xFFFFFFFF00000000ull};

// Returns the truth table of pObj in terms of the truth tables already in
// `tts` (the cut leaves), simulating and caching the cone in between.
static uint64_t Lsv_ConeTt(Abc_Obj_t* pObj,
                           std::unordered_map<int, uint64_t>& tts) {
  auto it = tts.find(Abc_ObjId(pObj));
  if (it != tts.end()) return it->second;
  uint64_t t0 = Lsv_ConeTt(Abc_ObjFanin0(pObj), tts);
  uint64_t t1 = Lsv_ConeTt(Abc_ObjFanin1(pObj), tts);
  if (Abc_ObjFaninC0(pObj)) t0 = ~t0;
  if (Abc_ObjFaninC1(pObj)) t1 = ~t1;
  return tts[Abc_ObjId(pObj)] = t0 & t1;
}

static uint64_t Lsv_CutTt(Abc_Obj_t* pObj, const Lsv_Cut& cut,
                          std::unordered_map<int, uint64_t>& tts) {
  tts.clear();
  for (int j = 0; j < cut.cut_size; j++)
    tts[cut.cut_nodes[j]] = s_VarTt[cut.cut_size - 1 - j];
  return Lsv_ConeTt(pObj, tts) & Lsv_TtMask(cut.cut_size);
}

static void Lsv_NtkEnumerateCuts(Abc_Ntk_t* pNtk, int k,
                                 std::vector<std::vector<Lsv_Cut>>& cuts) {
  cuts.assign(Abc_NtkObjNumMax(pNtk), std::vector<Lsv_Cut>());
  std::unordered_map<int, uint64_t> tts;
  Abc_Obj_t* pObj;
  int i;

  // Constant-1 node: the empty cut with the constant-1 function.
  Lsv_Cut empty;
  empty.cut_size = 0;
  empty.truth_table = 1;
  cuts[Abc_ObjId(Abc_AigConst1(pNtk))].push_back(empty);
  // Primary inputs: trivial cuts with the constant-2 function.
  Abc_NtkForEachCi(pNtk, pObj, i) {
    cuts[Abc_ObjId(pObj)].push_back(Lsv_CutTrivial(Abc_ObjId(pObj)));
  }

  // Internal nodes of a strashed AIG are created after their fanins, so ID order is
  // a topological order.
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    const std::vector<Lsv_Cut>& cuts0 = cuts[Abc_ObjFaninId0(pObj)];
    const std::vector<Lsv_Cut>& cuts1 = cuts[Abc_ObjFaninId1(pObj)];
    std::vector<Lsv_Cut>& res = cuts[id];

    res.push_back(Lsv_CutTrivial(id));
    Lsv_Cut cut;
    for (const Lsv_Cut& c0 : cuts0) {
      for (const Lsv_Cut& c1 : cuts1) {
        if (Lsv_CutMerge(c0, c1, k, cut)) Lsv_CutAdd(res, cut);
      }
    }

    // Truth tables are computed after all cuts of the node are collected.
    for (int j = 1; j < (int)res.size(); j++)
      res[j].truth_table = Lsv_CutTt(pObj, res[j], tts);
  }
}

static void Lsv_CutPrintPrefix(int id, const Lsv_Cut& cut) {
  printf("%d:", id);
  for (int j = 0; j < cut.cut_size; j++) printf(" %d", cut.cut_nodes[j]);
  printf(": ");
}

void Lsv_NtkCutTt(Abc_Ntk_t* pNtk, int k) {
  std::vector<std::vector<Lsv_Cut>> cuts;
  Lsv_NtkEnumerateCuts(pNtk, k, cuts);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const Lsv_Cut& cut : cuts[Abc_ObjId(pObj)]) {
      Lsv_CutPrintPrefix(Abc_ObjId(pObj), cut);
      printf("%llX\n", (unsigned long long)cut.truth_table);
    }
  }
}

static DdNode* Lsv_ConeBdd(DdManager* dd, Abc_Obj_t* pObj,
                           std::unordered_map<int, DdNode*>& bdds) {
  auto it = bdds.find(Abc_ObjId(pObj));
  if (it != bdds.end()) return it->second;
  DdNode* bdd0 = Lsv_ConeBdd(dd, Abc_ObjFanin0(pObj), bdds);
  DdNode* bdd1 = Lsv_ConeBdd(dd, Abc_ObjFanin1(pObj), bdds);
  DdNode* bdd = Cudd_bddAnd(dd, Cudd_NotCond(bdd0, Abc_ObjFaninC0(pObj)),
                            Cudd_NotCond(bdd1, Abc_ObjFaninC1(pObj)));
  Cudd_Ref(bdd);
  bdds[Abc_ObjId(pObj)] = bdd;
  return bdd;
}

void Lsv_NtkCutBddsize(Abc_Ntk_t* pNtk, int k) {
  std::vector<std::vector<Lsv_Cut>> cuts;
  Lsv_NtkEnumerateCuts(pNtk, k, cuts);

  // BDD variable j is the j-th smallest leaf ID of a cut, so the variable
  // order follows the node IDs. Dynamic reordering is off by default.
  DdManager* dd = Cudd_Init(6, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  std::unordered_map<int, DdNode*> bdds;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const Lsv_Cut& cut : cuts[Abc_ObjId(pObj)]) {
      bdds.clear();
      for (int j = 0; j < cut.cut_size; j++) {
        DdNode* var = Cudd_bddIthVar(dd, j);
        Cudd_Ref(var);
        bdds[cut.cut_nodes[j]] = var;
      }
      DdNode* bdd = Lsv_ConeBdd(dd, pObj, bdds);
      Lsv_CutPrintPrefix(Abc_ObjId(pObj), cut);
      printf("%d\n", Cudd_DagSize(bdd));
      for (auto& entry : bdds) Cudd_RecursiveDeref(dd, entry.second);
    }
  }
  Cudd_Quit(dd);
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (globalUtilOptind + 1 != argc) goto usage;
  k = atoi(argv[globalUtilOptind]);
  if (k < 2 || k > 6) {
    Abc_Print(-1, "k should be between 2 and 6.\n");
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
  Lsv_NtkCutTt(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt [-h] <k>\n");
  Abc_Print(-2, "\t        enumerates k-feasible cuts of each internal AIG node and prints their truth tables\n");
  Abc_Print(-2, "\t<k>   : maximum cut size (2 <= k <= 6)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandCutBddsize(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (globalUtilOptind + 1 != argc) goto usage;
  k = atoi(argv[globalUtilOptind]);
  if (k < 2 || k > 6) {
    Abc_Print(-1, "k should be between 2 and 6.\n");
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
  Lsv_NtkCutBddsize(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize [-h] <k>\n");
  Abc_Print(-2, "\t        enumerates k-feasible cuts of each internal AIG node and prints their BDD sizes\n");
  Abc_Print(-2, "\t<k>   : maximum cut size (2 <= k <= 6)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

