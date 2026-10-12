#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <cstdint>
#include <unordered_map>
#include <vector>

// ---------------------------------------------------------------------------
// PA1 problem 4: k-feasible cut enumeration + truth-table / BDD-size printing.
// Command names follow the spec: lsv_cut_tt <k> and lsv_cut_bddsize <k>.
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// lsv_print_nodes (kept from the course scaffold)
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
// Shared cut enumeration
// ---------------------------------------------------------------------------
typedef std::vector<int> Cut;  // sorted-ascending list of leaf node IDs

// Merge two sorted cuts into the union; return false if union exceeds k.
static bool MergeCuts(const Cut& a, const Cut& b, int k, Cut& out) {
  out.clear();
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] == b[j]) {
      out.push_back(a[i]);
      ++i;
      ++j;
    } else if (a[i] < b[j]) {
      out.push_back(a[i]);
      ++i;
    } else {
      out.push_back(b[j]);
      ++j;
    }
    if ((int)out.size() > k) return false;
  }
  while (i < a.size()) {
    out.push_back(a[i++]);
    if ((int)out.size() > k) return false;
  }
  while (j < b.size()) {
    out.push_back(b[j++]);
    if ((int)out.size() > k) return false;
  }
  return true;
}

// Compute the k-feasible cut set of every object, keyed by object id.
// cuts[id][0] is always the trivial cut {id}. Duplicate leaf-sets are removed.
static void ComputeCuts(Abc_Ntk_t* pNtk, int k,
                        std::vector<std::vector<Cut>>& cuts) {
  int maxId = Abc_NtkObjNumMax(pNtk);
  cuts.assign(maxId + 1, std::vector<Cut>());
  Abc_Obj_t* pObj;
  int i;

  // Constant node (if present) and CIs only have the trivial cut.
  Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
  if (pConst) cuts[Abc_ObjId(pConst)].push_back(Cut{(int)Abc_ObjId(pConst)});
  Abc_NtkForEachCi(pNtk, pObj, i) {
    cuts[Abc_ObjId(pObj)].push_back(Cut{(int)Abc_ObjId(pObj)});
  }

  // Internal AND nodes, iterated in id order (fanins already processed).
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    std::vector<Cut>& here = cuts[id];
    here.push_back(Cut{id});  // trivial cut first
    int id0 = Abc_ObjId(Abc_ObjFanin0(pObj));
    int id1 = Abc_ObjId(Abc_ObjFanin1(pObj));
    for (const Cut& c0 : cuts[id0]) {
      for (const Cut& c1 : cuts[id1]) {
        Cut merged;
        if (!MergeCuts(c0, c1, k, merged)) continue;
        bool dup = false;
        for (const Cut& e : here) {
          if (e == merged) {
            dup = true;
            break;
          }
        }
        if (!dup) here.push_back(merged);
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Truth-table computation for one cut
// ---------------------------------------------------------------------------
static uint64_t ElemVar(int idx, int nVars) {
  // Truth table of the idx-th cut input over nVars variables.
  uint64_t tt = 0;
  int rows = 1 << nVars;
  for (int r = 0; r < rows; ++r)
    if ((r >> idx) & 1) tt |= (uint64_t)1 << r;
  return tt;
}

static uint64_t TtDfs(Abc_Obj_t* pObj,
                      const std::unordered_map<int, int>& leafIdx, int nVars,
                      Abc_Obj_t* pConst,
                      std::unordered_map<int, uint64_t>& memo) {
  int id = Abc_ObjId(pObj);
  auto lit = leafIdx.find(id);
  if (lit != leafIdx.end()) return ElemVar(lit->second, nVars);
  if (pConst && pObj == pConst) {
    int rows = 1 << nVars;
    return (rows == 64) ? ~(uint64_t)0 : (((uint64_t)1 << rows) - 1);
  }
  auto mit = memo.find(id);
  if (mit != memo.end()) return mit->second;
  uint64_t t0 = TtDfs(Abc_ObjFanin0(pObj), leafIdx, nVars, pConst, memo);
  if (Abc_ObjFaninC0(pObj)) t0 = ~t0;
  uint64_t t1 = TtDfs(Abc_ObjFanin1(pObj), leafIdx, nVars, pConst, memo);
  if (Abc_ObjFaninC1(pObj)) t1 = ~t1;
  uint64_t res = t0 & t1;
  memo[id] = res;
  return res;
}

static uint64_t CutTruthTable(Abc_Ntk_t* pNtk, Abc_Obj_t* pRoot, const Cut& cut,
                              Abc_Obj_t* pConst) {
  int nVars = (int)cut.size();
  std::unordered_map<int, int> leafIdx;
  for (int j = 0; j < nVars; ++j) leafIdx[cut[j]] = j;
  std::unordered_map<int, uint64_t> memo;
  uint64_t tt = TtDfs(pRoot, leafIdx, nVars, pConst, memo);
  int rows = 1 << nVars;
  uint64_t mask = (rows == 64) ? ~(uint64_t)0 : (((uint64_t)1 << rows) - 1);
  return tt & mask;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not strashed (run \"strash\" first).\n");
    return 1;
  }
  if (argc != globalUtilOptind + 1) goto usage;
  {
    int k = atoi(argv[globalUtilOptind]);
    if (k < 2 || k > 6) {
      Abc_Print(-1, "k must be in the range [2, 6].\n");
      return 1;
    }
    std::vector<std::vector<Cut>> cuts;
    ComputeCuts(pNtk, k, cuts);
    Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      for (const Cut& cut : cuts[id]) {
        printf("%d:", id);
        for (int leaf : cut) printf(" %d", leaf);
        uint64_t tt = CutTruthTable(pNtk, pObj, cut, pConst);
        printf(": %llX\n", (unsigned long long)tt);
      }
    }
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
  Abc_Print(-2,
            "\t        enumerates k-feasible cuts of every internal AIG node\n"
            "\t        and prints each cut's truth table in hexadecimal\n");
  Abc_Print(-2, "\t<k>   : cut size, 2 <= k <= 6\n");
  return 1;
}

// ---------------------------------------------------------------------------
// BDD size computation for one cut (variable order = ascending node id)
// ---------------------------------------------------------------------------
static DdNode* BddDfs(DdManager* dd, Abc_Obj_t* pObj,
                      const std::unordered_map<int, int>& leafIdx,
                      Abc_Obj_t* pConst,
                      std::unordered_map<int, DdNode*>& memo) {
  int id = Abc_ObjId(pObj);
  auto lit = leafIdx.find(id);
  if (lit != leafIdx.end()) {
    DdNode* v = Cudd_bddIthVar(dd, lit->second);
    Cudd_Ref(v);
    return v;
  }
  if (pConst && pObj == pConst) {
    DdNode* one = Cudd_ReadOne(dd);
    Cudd_Ref(one);
    return one;
  }
  auto mit = memo.find(id);
  if (mit != memo.end()) {
    Cudd_Ref(mit->second);
    return mit->second;
  }
  DdNode* f0 = BddDfs(dd, Abc_ObjFanin0(pObj), leafIdx, pConst, memo);
  if (Abc_ObjFaninC0(pObj)) f0 = Cudd_Not(f0);
  DdNode* f1 = BddDfs(dd, Abc_ObjFanin1(pObj), leafIdx, pConst, memo);
  if (Abc_ObjFaninC1(pObj)) f1 = Cudd_Not(f1);
  DdNode* res = Cudd_bddAnd(dd, f0, f1);
  Cudd_Ref(res);
  Cudd_RecursiveDeref(dd, f0);
  Cudd_RecursiveDeref(dd, f1);
  memo[id] = res;
  Cudd_Ref(res);  // one ref held by memo, one returned to caller
  return res;
}

static int CutBddSize(Abc_Obj_t* pRoot, const Cut& cut, Abc_Obj_t* pConst) {
  int nVars = (int)cut.size();
  DdManager* dd = Cudd_Init(nVars, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  std::unordered_map<int, int> leafIdx;
  for (int j = 0; j < nVars; ++j) leafIdx[cut[j]] = j;
  std::unordered_map<int, DdNode*> memo;
  DdNode* root = BddDfs(dd, pRoot, leafIdx, pConst, memo);
  int size = Cudd_DagSize(root);
  Cudd_RecursiveDeref(dd, root);
  for (auto& kv : memo) Cudd_RecursiveDeref(dd, kv.second);
  Cudd_Quit(dd);
  return size;
}

int Lsv_CommandCutBddsize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not strashed (run \"strash\" first).\n");
    return 1;
  }
  if (argc != globalUtilOptind + 1) goto usage;
  {
    int k = atoi(argv[globalUtilOptind]);
    if (k < 2 || k > 6) {
      Abc_Print(-1, "k must be in the range [2, 6].\n");
      return 1;
    }
    std::vector<std::vector<Cut>> cuts;
    ComputeCuts(pNtk, k, cuts);
    Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      for (const Cut& cut : cuts[id]) {
        printf("%d:", id);
        for (int leaf : cut) printf(" %d", leaf);
        int size = CutBddSize(pObj, cut, pConst);
        printf(": %d\n", size);
      }
    }
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
  Abc_Print(-2,
            "\t        enumerates k-feasible cuts of every internal AIG node\n"
            "\t        and prints each cut's ROBDD size (Cudd_DagSize)\n");
  Abc_Print(-2, "\t<k>   : cut size, 2 <= k <= 6\n");
  return 1;
}
