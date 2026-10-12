#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <algorithm>
#include <iterator>
#include <cstdint>
#include <unordered_map>
#include "bdd/cudd/cudd.h"

typedef std::vector<std::vector<std::vector<unsigned int>>> NtkCuts_t;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTruthTable(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTruthTable, 0);
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

static uint64_t Lsv_NodeTruthTable(Abc_Obj_t* pObj, std::unordered_map<unsigned int, uint64_t>& val) {
  if (val.count(Abc_ObjId(pObj))) return val[Abc_ObjId(pObj)];
  uint64_t input0 = Lsv_NodeTruthTable(Abc_ObjFanin0(pObj), val);
  uint64_t input1 = Lsv_NodeTruthTable(Abc_ObjFanin1(pObj), val);
  uint64_t output = (Abc_ObjFaninC0(pObj) ? ~input0 : input0) & (Abc_ObjFaninC1(pObj) ? ~input1 : input1);
  val[Abc_ObjId(pObj)] = output;
  return output;
}

static uint64_t Lsv_CutTruthTable(Abc_Obj_t* pRoot, const std::vector<unsigned int>& cut) {
  std::unordered_map<unsigned int, uint64_t> val;
  int nLeaf = cut.size();
  int i = 0;
  for (auto leafId: cut) {
    for (int j = 0; j < (1 << nLeaf); j++) {
      if ((j / (1 << (nLeaf - i - 1))) % 2) {
        val[leafId] |= (1ULL << j);
      }
    }
    i++;
  }
  uint64_t mask = ((1 << nLeaf) == 64) ? ~0ULL : ((1ULL << (1 << nLeaf)) - 1);
  uint64_t output = Lsv_NodeTruthTable(pRoot, val);
  return output & mask;
}

static NtkCuts_t Lsv_NtkEnumerateCuts(Abc_Ntk_t* pNtk, int k) {
  NtkCuts_t NtkCuts(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPi(pNtk, pObj, i) {
    NtkCuts[Abc_ObjId(pObj)].push_back({Abc_ObjId(pObj)});
  }
  Abc_NtkForEachNode(pNtk, pObj, i) {
    NtkCuts[Abc_ObjId(pObj)].push_back({Abc_ObjId(pObj)});
    for (const auto& cut0: NtkCuts[Abc_ObjFaninId0(pObj)]) {
      for (const auto& cut1: NtkCuts[Abc_ObjFaninId1(pObj)]) {
        std::vector<unsigned int> newCut;
        std::set_union(cut0.begin(), cut0.end(), cut1.begin(), cut1.end(), std::back_inserter(newCut));
        NtkCuts[Abc_ObjId(pObj)].push_back(newCut);
      }
    }
    std::sort(NtkCuts[Abc_ObjId(pObj)].begin(), NtkCuts[Abc_ObjId(pObj)].end(),
              [](const std::vector<unsigned int>& a, const std::vector<unsigned int>& b) {
                if (a.size() != b.size()) return a.size() < b.size();
                return a < b;
              });
    NtkCuts[Abc_ObjId(pObj)].erase(std::unique(NtkCuts[Abc_ObjId(pObj)].begin(), NtkCuts[Abc_ObjId(pObj)].end()),
                                   NtkCuts[Abc_ObjId(pObj)].end());
    std::vector<std::vector<unsigned int>> kept;
    for (const auto& cut0: NtkCuts[Abc_ObjId(pObj)]) {
      if (cut0.size() > k) {
        continue;
      }
      bool dominated = false;
      for (const auto& cut1: NtkCuts[Abc_ObjId(pObj)]) {
        if (std::includes(cut0.begin(), cut0.end(), cut1.begin(), cut1.end()) && !(cut0 == cut1)) {
          dominated = true;
          break;
        }
      }
      if (!dominated){
        kept.push_back(cut0);
      }
    }
    NtkCuts[Abc_ObjId(pObj)] = std::move(kept);
  }
  return NtkCuts;
}

static void Lsv_NtkCutTruthTable(Abc_Ntk_t* pNtk, int k) {
  NtkCuts_t NtkCuts = Lsv_NtkEnumerateCuts(pNtk, k);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const auto& cut: NtkCuts[Abc_ObjId(pObj)]) {
      printf("%u:", Abc_ObjId(pObj));
      for (auto nodeId: cut) {
        printf(" %u", nodeId);
      }
      printf(": %llX\n", (unsigned long long)Lsv_CutTruthTable(pObj, cut));
    }
  }
}

int Lsv_CommandCutTruthTable(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (argc != globalUtilOptind + 1) {
    Abc_Print(-1, "Missing or extra argument.\n");
    goto usage;
  }
  k = atoi(argv[globalUtilOptind]);
  if (k < 1 || k > 6) {
    Abc_Print(-1, "k must be between 1 and 6 (truth table must fit in 64 bits).\n");
    return 1;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not an AIG (run \"strash\").\n");
    return 1;
  }
  Lsv_NtkCutTruthTable(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt [-h] <k>\n");
  Abc_Print(-2, "\t        prints all k-feasible cuts rooted at internal nodes of an AIG and the corresponding truth table for each cut\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

static DdNode* Lsv_NodeBdd(DdManager* dd, Abc_Obj_t* pObj, std::unordered_map<unsigned int, DdNode*>& bdd) {
  if (bdd.count(Abc_ObjId(pObj))) return bdd[Abc_ObjId(pObj)];
  DdNode* input0 = Lsv_NodeBdd(dd, Abc_ObjFanin0(pObj), bdd);
  DdNode* input1 = Lsv_NodeBdd(dd, Abc_ObjFanin1(pObj), bdd);
  DdNode* output = Cudd_bddAnd(dd, Cudd_NotCond(input0, Abc_ObjFaninC0(pObj)), Cudd_NotCond(input1, Abc_ObjFaninC1(pObj)));
  Cudd_Ref(output);
  bdd[Abc_ObjId(pObj)] = output;
  return output;
}

static int Lsv_CutBddSize(DdManager* dd, Abc_Obj_t* pRoot, const std::vector<unsigned int>& cut) {
  // cut is sorted by node ID, so the i-th leaf gets the i-th BDD variable (closer to the root)
  std::unordered_map<unsigned int, DdNode*> bdd;
  int i = 0;
  for (auto leafId: cut) {
    DdNode* var = Cudd_bddIthVar(dd, i++);
    Cudd_Ref(var);
    bdd[leafId] = var;
  }
  int size = Cudd_DagSize(Lsv_NodeBdd(dd, pRoot, bdd));
  for (auto& entry: bdd) {
    Cudd_RecursiveDeref(dd, entry.second);
  }
  return size;
}

static void Lsv_NtkCutBddSize(Abc_Ntk_t* pNtk, int k) {
  NtkCuts_t NtkCuts = Lsv_NtkEnumerateCuts(pNtk, k);
  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const auto& cut: NtkCuts[Abc_ObjId(pObj)]) {
      printf("%u:", Abc_ObjId(pObj));
      for (auto nodeId: cut) {
        printf(" %u", nodeId);
      }
      printf(": %d\n", Lsv_CutBddSize(dd, pObj, cut));
    }
  }
  Cudd_Quit(dd);
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (argc != globalUtilOptind + 1) {
    Abc_Print(-1, "Missing or extra argument.\n");
    goto usage;
  }
  k = atoi(argv[globalUtilOptind]);
  if (k < 1) {
    Abc_Print(-1, "k must be a positive integer.\n");
    return 1;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not an AIG (run \"strash\").\n");
    return 1;
  }
  Lsv_NtkCutBddSize(pNtk, k);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize [-h] <k>\n");
  Abc_Print(-2, "\t        prints all k-feasible cuts rooted at internal nodes of an AIG and the corresponding BDD size for each cut\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}