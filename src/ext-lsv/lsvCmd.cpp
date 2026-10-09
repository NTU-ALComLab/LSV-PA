#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <vector>
#include <algorithm>
#include <cstdint>
#include <iterator>
#include <unordered_map>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBDDSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBDDSize, 0);
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

// Merges two sorted cuts into out; gives up as soon as the union exceeds k leaves.
static bool Lsv_MergeCut(const std::vector<int>& a, const std::vector<int>& b, int k, std::vector<int>& out) {
  out.clear();
  size_t i = 0, j = 0;
  while (i < a.size() || j < b.size()) {
    if (j == b.size() || (i < a.size() && a[i] < b[j])) out.push_back(a[i++]);
    else if (i == a.size() || b[j] < a[i]) out.push_back(b[j++]);
    else { out.push_back(a[i++]); j++; }
    if ((int)out.size() > k) return false;
  }
  return true;
}

// 64-bit signature of a cut: bit (id % 64) is set for every leaf.
// popcount(signA | signB) never exceeds |A U B|, so it rejects oversized merges cheaply.
static uint64_t Lsv_CutSign(const std::vector<int>& cut) {
  uint64_t sign = 0;
  for (int x : cut) sign |= 1ULL << (x & 63);
  return sign;
}

static void Lsv_EnumerateCuts(Abc_Ntk_t* pNtk, int k, std::vector<std::vector<std::vector<int>>>& cuts) {
  Abc_Obj_t* pObj;
  int i;
  cuts.assign(Abc_NtkObjNumMax(pNtk), {});
  std::vector<std::vector<uint64_t>> signs(Abc_NtkObjNumMax(pNtk));
  Abc_NtkForEachPi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    cuts[id] = { {id} };
    signs[id] = { Lsv_CutSign(cuts[id][0]) };
  }
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    int id0 = Abc_ObjId(Abc_ObjFanin0(pObj));
    int id1 = Abc_ObjId(Abc_ObjFanin1(pObj));

    cuts[id].push_back({id});
    signs[id].push_back(Lsv_CutSign(cuts[id][0]));
    std::vector<int> tmp;
    for (size_t a = 0; a < cuts[id0].size(); a++) {
      for (size_t b = 0; b < cuts[id1].size(); b++) {
        if (__builtin_popcountll(signs[id0][a] | signs[id1][b]) > k) continue;
        if (!Lsv_MergeCut(cuts[id0][a], cuts[id1][b], k, tmp)) continue;
        if (std::find(cuts[id].begin(), cuts[id].end(), tmp) == cuts[id].end()) {
          cuts[id].push_back(tmp);
          signs[id].push_back(Lsv_CutSign(tmp));
        }
      }
    }
  }
}

static uint64_t Lsv_EvalNode(Abc_Obj_t* pObj, std::unordered_map<int, uint64_t>& memo) {
  int id = Abc_ObjId(pObj);
  auto it = memo.find(id);
  if (it != memo.end()) return it->second;

  uint64_t t0 = Lsv_EvalNode(Abc_ObjFanin0(pObj), memo);
  uint64_t t1 = Lsv_EvalNode(Abc_ObjFanin1(pObj), memo);
  if (Abc_ObjFaninC0(pObj)) t0 = ~t0;
  if (Abc_ObjFaninC1(pObj)) t1 = ~t1;

  return memo[id] = (t0 & t1);
}

// Keeps the low 2^m bits of a truth table over m variables.
static uint64_t Lsv_Mask(int m) {
  if (m == 6) return ~0ULL;
  return (1ULL << (1 << m)) - 1;
}

static uint64_t Lsv_CutTruthTable(Abc_Obj_t* pRoot, const std::vector<int>& cut) {
  int m = cut.size();
  std::unordered_map<int, uint64_t> memo;
  for (int i = 0; i < m; i++) {
    uint64_t tt = 0;
    for (int idx = 0; idx < (1 << m); idx++) {
      if ((idx >> (m - 1 - i)) & 1) tt |= (1ULL << idx);  // cut[0] is the MSB
    }
    memo[cut[i]] = tt;
  }
  return Lsv_EvalNode(pRoot, memo) & Lsv_Mask(m);
}

void Lsv_NtkCutTT(Abc_Ntk_t* pNtk, int k) {
  std::vector<std::vector<std::vector<int>>> cuts;
  Abc_Obj_t* pObj;
  int i;
  Lsv_EnumerateCuts(pNtk, k, cuts);
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const auto& cut : cuts[id]) {
      printf("%d:", id);
      for (int x : cut) printf(" %d", x);
      printf(": %llX\n", (unsigned long long)Lsv_CutTruthTable(pObj, cut));
    }
  }
}

// Builds the BDD of pObj over the cut leaves already stored in memo.
// Every node created here is referenced and must be dereferenced by the caller.
static DdNode* Lsv_BuildBdd(Abc_Obj_t* pObj, std::unordered_map<int, DdNode*>& memo, DdManager* dd) {
  int id = Abc_ObjId(pObj);
  auto it = memo.find(id);
  if (it != memo.end()) return it->second;

  DdNode* f0 = Lsv_BuildBdd(Abc_ObjFanin0(pObj), memo, dd);
  DdNode* f1 = Lsv_BuildBdd(Abc_ObjFanin1(pObj), memo, dd);
  f0 = Cudd_NotCond(f0, Abc_ObjFaninC0(pObj));
  f1 = Cudd_NotCond(f1, Abc_ObjFaninC1(pObj));

  DdNode* r = Cudd_bddAnd(dd, f0, f1);
  Cudd_Ref(r);
  return memo[id] = r;
}

static int Lsv_CutBddSize(DdManager* dd, Abc_Obj_t* pRoot, const std::vector<int>& cut) {
  std::unordered_map<int, DdNode*> memo;
  for (size_t j = 0; j < cut.size(); j++) {
    memo[cut[j]] = Cudd_bddIthVar(dd, j);  // cut[0] has the smallest ID and sits closest to the root
  }
  int size = Cudd_DagSize(Lsv_BuildBdd(pRoot, memo, dd));
  for (const auto& entry : memo) {
    if (std::find(cut.begin(), cut.end(), entry.first) == cut.end()) {
      Cudd_RecursiveDeref(dd, entry.second);
    }
  }
  return size;
}

void Lsv_NtkCutBDDSize(Abc_Ntk_t* pNtk, int k) {
  std::vector<std::vector<std::vector<int>>> cuts;
  Abc_Obj_t* pObj;
  int i;
  Lsv_EnumerateCuts(pNtk, k, cuts);
  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const auto& cut : cuts[id]) {
      printf("%d:", id);
      for (int x : cut) printf(" %d", x);
      printf(": %d\n", Lsv_CutBddSize(dd, pObj, cut));
    }
  }
  Cudd_Quit(dd);
}

int Lsv_CommandCutBDDSize(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (k < 2 || k > 6) {
    Abc_Print(-1, "k should be in [2, 6].\n");
    return 1;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG. Run \"strash\" first.\n");
    return 1;
  }
  Lsv_NtkCutBDDSize(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize [-h] <k>\n");
  Abc_Print(-2, "\t        enumerates k-feasible cuts and prints the BDD size of each cut\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (k < 2 || k > 6) {
    Abc_Print(-1, "k should be in [2, 6].\n");
    return 1;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG. Run \"strash\" first.\n");
    return 1;
  }
  Lsv_NtkCutTT(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt [-h] <k>\n");
  Abc_Print(-2, "\t        enumerates k-feasible cuts and prints their truth tables\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
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