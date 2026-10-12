#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <algorithm>
#include <cerrno>
#include <cinttypes>
#include <cstdint>
#include <memory>
#include <vector>

#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"
#endif

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

namespace {

struct Cut {
  int leaves[6] = {};
  int size = 0;
  uint64_t truth = 0;
  uint64_t signature = 0;
};

uint64_t TruthMask(int size) {
  return size == 6 ? UINT64_MAX : (uint64_t(1) << (1 << size)) - 1;
}

Cut Singleton(int id) {
  Cut cut;
  cut.leaves[0] = id;
  cut.size = 1;
  cut.truth = 2;
  cut.signature = uint64_t(1) << (id % 64);
  return cut;
}

bool MergeLeaves(const Cut& a, const Cut& b, int k, Cut& result) {
  int i = 0, j = 0;
  while (i < a.size || j < b.size) {
    if (result.size == k)
      return false;
    int id;
    if (j == b.size || (i < a.size && a.leaves[i] < b.leaves[j]))
      id = a.leaves[i++];
    else if (i == a.size || b.leaves[j] < a.leaves[i])
      id = b.leaves[j++];
    else {
      id = a.leaves[i++];
      ++j;
    }
    result.leaves[result.size++] = id;
  }
  result.signature = a.signature | b.signature;
  return true;
}

bool IsSubset(const Cut& a, const Cut& b) {
  return a.size <= b.size && (a.signature & ~b.signature) == 0 &&
         std::includes(b.leaves, b.leaves + b.size,
                       a.leaves, a.leaves + a.size);
}

uint64_t RemapTruth(const Cut& child, const Cut& merged) {
  int positions[6];
  for (int i = 0, j = 0; i < child.size; ++i) {
    while (merged.leaves[j] != child.leaves[i])
      ++j;
    positions[i] = merged.size - 1 - j;
  }
  uint64_t truth = 0;
  for (int assignment = 0; assignment < (1 << merged.size); ++assignment) {
    int index = 0;
    for (int i = 0; i < child.size; ++i)
      index = (index << 1) | ((assignment >> positions[i]) & 1);
    truth |= ((child.truth >> index) & 1) << assignment;
  }
  return truth;
}

#ifdef ABC_USE_CUDD
// Each successful call returns one reference, including constant cofactors.
DdNode* BuildBdd(DdManager* manager, uint64_t truth, int size, int variable) {
  if (truth == 0 || truth == TruthMask(size)) {
    DdNode* result = Cudd_NotCond(Cudd_ReadOne(manager), truth == 0);
    Cudd_Ref(result);
    return result;
  }
  const int half = 1 << (size - 1);
  DdNode* low = BuildBdd(manager, truth & TruthMask(size - 1),
                       size - 1, variable + 1);
  if (!low)
    return nullptr;
  DdNode* high = BuildBdd(manager, truth >> half, size - 1, variable + 1);
  if (!high) {
    Cudd_RecursiveDeref(manager, low);
    return nullptr;
  }
  DdNode* var = Cudd_bddIthVar(manager, variable);
  DdNode* result = var ? Cudd_bddIte(manager, var, high, low) : nullptr;
  if (result)
    Cudd_Ref(result);
  Cudd_RecursiveDeref(manager, low);
  Cudd_RecursiveDeref(manager, high);
  return result;
}
#endif

int PrintCuts(Abc_Ntk_t* network, int k, bool bddSize) {
#ifdef ABC_USE_CUDD
  std::unique_ptr<DdManager, decltype(&Cudd_Quit)> manager(
      bddSize ? Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0) : nullptr,
      Cudd_Quit);
  if (bddSize && !manager) {
    Abc_Print(-1, "Cannot initialize the CUDD manager.\n");
    return 1;
  }
  if (manager)
    Cudd_AutodynDisable(manager.get());
#endif
  std::vector<std::vector<Cut>> cuts(Abc_NtkObjNumMax(network));
  Cut constant;
  constant.truth = 1;
  cuts[Abc_ObjId(Abc_AigConst1(network))].push_back(constant);
  Abc_Obj_t* node;
  int i;
  Abc_NtkForEachPi(network, node, i)
    cuts[Abc_ObjId(node)].push_back(Singleton(Abc_ObjId(node)));

  std::unique_ptr<Vec_Ptr_t, decltype(&Vec_PtrFree)> order(
      Abc_NtkDfs(network, 1), Vec_PtrFree);
  Vec_PtrForEachEntry(Abc_Obj_t*, order.get(), node, i) {
    std::vector<Cut>& result = cuts[Abc_ObjId(node)];
    result.push_back(Singleton(Abc_ObjId(node)));
    for (const Cut& a : cuts[Abc_ObjFaninId0(node)]) {
      for (const Cut& b : cuts[Abc_ObjFaninId1(node)]) {
        Cut merged;
        if (!MergeLeaves(a, b, k, merged))
          continue;
        if (std::any_of(result.begin(), result.end(),
                        [&](const Cut& cut) { return IsSubset(cut, merged); }))
          continue;
        result.erase(std::remove_if(result.begin(), result.end(),
                                    [&](const Cut& cut) {
                                      return IsSubset(merged, cut);
                                    }), result.end());
        uint64_t left = RemapTruth(a, merged);
        uint64_t right = RemapTruth(b, merged);
        if (Abc_ObjFaninC0(node))
          left = ~left;
        if (Abc_ObjFaninC1(node))
          right = ~right;
        merged.truth = left & right & TruthMask(merged.size);
        result.push_back(merged);
      }
    }
    for (const Cut& cut : result) {
      int size = 0;
#ifdef ABC_USE_CUDD
      if (bddSize) {
        DdNode* root = BuildBdd(manager.get(), cut.truth, cut.size, 0);
        if (!root) {
          Abc_Print(-1, "CUDD failed while building a cut BDD at node %d.\n",
                    Abc_ObjId(node));
          return 1;
        }
        size = Cudd_DagSize(root);
        Cudd_RecursiveDeref(manager.get(), root);
        if (size <= 0) {
          Abc_Print(-1, "CUDD failed while counting a cut BDD at node %d.\n",
                    Abc_ObjId(node));
          return 1;
        }
      }
#endif
      printf("%d:", Abc_ObjId(node));
      for (int j = 0; j < cut.size; ++j)
        printf(" %d", cut.leaves[j]);
      if (bddSize)
        printf(": %d\n", size);
      else
        printf(": %" PRIX64 "\n", cut.truth);
    }
  }
  return 0;
}

int CommandCuts(Abc_Frame_t* frame, int argc, char** argv, bool bddSize) {
  if (argc == 2 && !strcmp(argv[1], "-h")) {
    Abc_Print(-2, "usage: %s <k>  (or %s -h)\n", argv[0], argv[0]);
    Abc_Print(-2, "\t        prints %s for irredundant cuts of a combinational AIG\n",
              bddSize ? "BDD DAG sizes" : "truth tables");
    Abc_Print(-2, "\t        leaves are sorted; the first leaf is variable 0 (MSB)\n");
    Abc_Print(-2, "\t        %s\n", bddSize ? "sizes include the regular terminal" :
              "assignment 0 is bit 0; tables use the actual cut width");
    Abc_Print(-2, "\tk     : maximum cut size (2 through 6)\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  if (argc != 2) {
    Abc_Print(-1, "%s requires exactly one integer k (2 through 6).\n", argv[0]);
    return 1;
  }
  char* end;
  errno = 0;
  const long k = strtol(argv[1], &end, 10);
  const char first = argv[1][0];
  if (errno == ERANGE || end == argv[1] || *end ||
      !((first >= '0' && first <= '9') || first == '+' || first == '-') ||
      k < 2 || k > 6) {
    Abc_Print(-1, "Invalid k: expected an integer from 2 through 6.\n");
    return 1;
  }
  Abc_Ntk_t* network = Abc_FrameReadNtk(frame);
  if (!network) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsComb(network)) {
    Abc_Print(-1, "The network must be combinational (no latches).\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(network)) {
    Abc_Print(-1, "The network must be a strashed AIG; run strash first.\n");
    return 1;
  }
#ifndef ABC_USE_CUDD
  if (bddSize) {
    Abc_Print(-1, "lsv_cut_bddsize requires a build with CUDD support.\n");
    return 1;
  }
#endif
  return PrintCuts(network, static_cast<int>(k), bddSize);
}

}  // namespace

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  return CommandCuts(pAbc, argc, argv, false);
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  return CommandCuts(pAbc, argc, argv, true);
}