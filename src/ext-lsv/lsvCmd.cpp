#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <iterator>
#include <set>
#include <unordered_map>
#include <vector>

using namespace std;

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
// PA1 Ex 4: lsv_cut_tt / lsv_cut_bddsize
// ---------------------------------------------------------------------------

typedef vector<int> LsvCut;           // leaf IDs, sorted ascending
typedef vector<LsvCut> LsvCutList;    // all cuts of one node

// Enumerates all k-feasible cuts of every PI and AND node.
// The result is indexed by object ID; other objects get an empty list.
// Cut order per AND node: trivial cut first, then unions of
// (fanin0 cut) x (fanin1 cut) in nested-loop order, skipping duplicates.
static vector<LsvCutList> Lsv_NtkEnumerateCuts(Abc_Ntk_t* pNtk, int k) {
  vector<LsvCutList> cuts(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachPi(pNtk, pObj, i) {
    cuts[Abc_ObjId(pObj)].push_back(LsvCut(1, Abc_ObjId(pObj)));
  }

  // In a strashed AIG, node IDs are in topological order,
  // so both fanins are processed before the node itself.
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    const LsvCutList& cuts0 = cuts[Abc_ObjFaninId0(pObj)];
    const LsvCutList& cuts1 = cuts[Abc_ObjFaninId1(pObj)];
    LsvCutList& result = cuts[id];
    set<LsvCut> seen;

    LsvCut trivial(1, id);
    result.push_back(trivial);
    seen.insert(trivial);

    LsvCut merged;
    for (const LsvCut& c0 : cuts0) {
      for (const LsvCut& c1 : cuts1) {
        merged.clear();
        set_union(c0.begin(), c0.end(), c1.begin(), c1.end(),
                       back_inserter(merged));
        if ((int)merged.size() > k) continue;
        if (seen.insert(merged).second) result.push_back(merged);
      }
    }
  }
  return cuts;
}

static void Lsv_PrintCut(int id, const LsvCut& cut) {
  printf("%d:", id);
  for (int leaf : cut) printf(" %d", leaf);
}

// Returns the truth table of `id` over the cut leaves (memoized in `memo`,
// which must be pre-filled with the leaves' elementary truth tables).
static word Lsv_ConeTruth(Abc_Ntk_t* pNtk, int id, word mask,
                          unordered_map<int, word>& memo) {
  auto it = memo.find(id);
  if (it != memo.end()) return it->second;
  Abc_Obj_t* pObj = Abc_NtkObj(pNtk, id);
  word tt0 = Lsv_ConeTruth(pNtk, Abc_ObjFaninId0(pObj), mask, memo);
  word tt1 = Lsv_ConeTruth(pNtk, Abc_ObjFaninId1(pObj), mask, memo);
  if (Abc_ObjFaninC0(pObj)) tt0 = ~tt0 & mask;
  if (Abc_ObjFaninC1(pObj)) tt1 = ~tt1 & mask;
  return memo[id] = tt0 & tt1;
}

// Truth table of node `id` w.r.t. `cut`. Leaf cut[0] (smallest ID) is the MSB
// of the assignment index; assignment 00...0 maps to the LSB of the result.
static word Lsv_CutTruth(Abc_Ntk_t* pNtk, int id, const LsvCut& cut) {
  int m = cut.size();
  int nBits = 1 << m;
  word mask = (nBits == 64) ? ~(word)0 : (((word)1 << nBits) - 1);

  unordered_map<int, word> memo;
  for (int j = 0; j < m; j++) {
    int bit = m - 1 - j;
    word tt = 0;
    for (int a = 0; a < nBits; a++)
      if ((a >> bit) & 1) tt |= (word)1 << a;
    memo[cut[j]] = tt;
  }
  return Lsv_ConeTruth(pNtk, id, mask, memo);
}

void Lsv_NtkCutTt(Abc_Ntk_t* pNtk, int k) {
  vector<LsvCutList> cuts = Lsv_NtkEnumerateCuts(pNtk, k);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const LsvCut& cut : cuts[id]) {
      Lsv_PrintCut(id, cut);
      printf(": %llX\n", (unsigned long long)Lsv_CutTruth(pNtk, id, cut));
    }
  }
}

// Returns the BDD of `id` over the cut leaves (memoized in `memo`, which must
// be pre-filled with the leaves' variables). Every node in `memo` holds one
// reference, which the caller releases.
static DdNode* Lsv_ConeBdd(DdManager* dd, Abc_Ntk_t* pNtk, int id,
                           unordered_map<int, DdNode*>& memo) {
  auto it = memo.find(id);
  if (it != memo.end()) return it->second;
  Abc_Obj_t* pObj = Abc_NtkObj(pNtk, id);
  DdNode* bFan0 = Lsv_ConeBdd(dd, pNtk, Abc_ObjFaninId0(pObj), memo);
  DdNode* bFan1 = Lsv_ConeBdd(dd, pNtk, Abc_ObjFaninId1(pObj), memo);
  DdNode* bRes = Cudd_bddAnd(dd, Cudd_NotCond(bFan0, Abc_ObjFaninC0(pObj)),
                             Cudd_NotCond(bFan1, Abc_ObjFaninC1(pObj)));
  Cudd_Ref(bRes);
  return memo[id] = bRes;
}

// ROBDD size of node `id` w.r.t. `cut`. Leaf cut[j] uses BDD variable j, so
// leaves with smaller IDs are closer to the root.
static int Lsv_CutBddSize(DdManager* dd, Abc_Ntk_t* pNtk, int id,
                          const LsvCut& cut) {
  unordered_map<int, DdNode*> memo;
  for (int j = 0; j < (int)cut.size(); j++) {
    DdNode* bVar = Cudd_bddIthVar(dd, j);
    Cudd_Ref(bVar);
    memo[cut[j]] = bVar;
  }
  int size = Cudd_DagSize(Lsv_ConeBdd(dd, pNtk, id, memo));
  for (auto& entry : memo) Cudd_RecursiveDeref(dd, entry.second);
  return size;
}

void Lsv_NtkCutBddSize(Abc_Ntk_t* pNtk, int k) {
  vector<LsvCutList> cuts = Lsv_NtkEnumerateCuts(pNtk, k);
  // One manager for all cuts: the variable order depends only on the
  // leaf position inside a cut, and reordering is disabled to keep it fixed.
  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Cudd_AutodynDisable(dd);

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const LsvCut& cut : cuts[id]) {
      Lsv_PrintCut(id, cut);
      printf(": %d\n", Lsv_CutBddSize(dd, pNtk, id, cut));
    }
  }
  Cudd_Quit(dd);
}

// Shared argument handling: parses <k> and checks the network.
// Returns k on success, or -1 if the usage should be printed.
static int Lsv_ParseCutArgs(Abc_Frame_t* pAbc, int argc, char** argv,
                            Abc_Ntk_t** ppNtk) {
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
      default:
        return -1;
    }
  }
  if (argc != globalUtilOptind + 1) return -1;
  int k = atoi(argv[globalUtilOptind]);
  if (k < 2 || k > 6) {
    Abc_Print(-1, "k must be in the range 2..6.\n");
    return -1;
  }
  *ppNtk = Abc_FrameReadNtk(pAbc);
  return k;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = NULL;
  int k = Lsv_ParseCutArgs(pAbc, argc, argv, &pNtk);
  if (k < 0) goto usage;
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG. Run \"strash\" first.\n");
    return 1;
  }
  Lsv_NtkCutTt(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt [-h] <k>\n");
  Abc_Print(-2, "\t        prints k-feasible cuts of each AND node and their truth tables\n");
  Abc_Print(-2, "\t<k>   : maximum cut size (2..6)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = NULL;
  int k = Lsv_ParseCutArgs(pAbc, argc, argv, &pNtk);
  if (k < 0) goto usage;
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG. Run \"strash\" first.\n");
    return 1;
  }
  Lsv_NtkCutBddSize(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize [-h] <k>\n");
  Abc_Print(-2, "\t        prints k-feasible cuts of each AND node and their ROBDD sizes\n");
  Abc_Print(-2, "\t<k>   : maximum cut size (2..6)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
