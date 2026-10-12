#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iterator>
#include <vector>

static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc,
                                 char** argv);
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTruthTable(Abc_Frame_t* pAbc, int argc,
                                    char** argv);
struct LsvCut {
  std::vector<int> leaves;
  uint64_t truth;
};

static void Lsv_InitializeLeafCuts(
    Abc_Ntk_t* pNtk, std::vector<std::vector<LsvCut>>& cuts) {
  Abc_Obj_t* pCi;
  int i;
  Abc_NtkForEachCi(pNtk, pCi, i) {
    LsvCut cut;
    cut.leaves.push_back(Abc_ObjId(pCi));
    cut.truth = 0x2;
    cuts[Abc_ObjId(pCi)].push_back(cut);
  }

  Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
  if (pConst != nullptr) {
    LsvCut cut;
    cut.truth = 0x1;
    cuts[Abc_ObjId(pConst)].push_back(cut);
  }
}

static void Lsv_PrintLeaves(const std::vector<int>& leaves) {
  for (size_t i = 0; i < leaves.size(); ++i) {
    if (i > 0) {
      printf(" ");
    }
    printf("%d", leaves[i]);
  }
}

static bool Lsv_MergeLeaves(const std::vector<int>& first,
                            const std::vector<int>& second, int k,
                            std::vector<int>& merged) {
  merged.clear();

  std::set_union(first.begin(), first.end(), second.begin(), second.end(),
                 std::back_inserter(merged));

  return static_cast<int>(merged.size()) <= k;
}

static bool Lsv_CutExists(const std::vector<LsvCut>& cuts,
                          const std::vector<int>& leaves) {
  for (const LsvCut& cut : cuts) {
    if (cut.leaves == leaves) {
      return true;
    }
  }
  return false;
}

static int Lsv_EvalNode(Abc_Obj_t* pObj, std::vector<int>& values) {
  int nodeId = Abc_ObjId(pObj);

  if (values[nodeId] != -1) {
    return values[nodeId];
  }

  if (Abc_AigNodeIsConst(pObj)) {
    values[nodeId] = 1;
    return 1;
  }

  Abc_Obj_t* fanin0 = Abc_ObjFanin0(pObj);
  Abc_Obj_t* fanin1 = Abc_ObjFanin1(pObj);

  int value0 = Lsv_EvalNode(fanin0, values);
  int value1 = Lsv_EvalNode(fanin1, values);

  if (Abc_ObjFaninC0(pObj)) {
    value0 = !value0;
  }
  if (Abc_ObjFaninC1(pObj)) {
    value1 = !value1;
  }

  values[nodeId] = value0 & value1;
  return values[nodeId];
}

static uint64_t Lsv_ComputeTruth(Abc_Obj_t* root,
                                 const std::vector<int>& leaves,
                                 int maxObjects) {
  uint64_t truth = 0;
  uint64_t assignments = 1ULL << leaves.size();

  for (uint64_t assignment = 0; assignment < assignments; ++assignment) {
    std::vector<int> values(maxObjects, -1);

    for (size_t i = 0; i < leaves.size(); ++i) {
      size_t shift = leaves.size() - 1 - i;
      values[leaves[i]] = (assignment >> shift) & 1;
    }

    int result = Lsv_EvalNode(root, values);

    if (result) {
      truth |= (1ULL << assignment);
    }
  }

  return truth;
}

static DdNode* Lsv_BuildBdd(DdManager* dd,
                            const std::vector<int>& leaves,
                            uint64_t truth,
                            size_t position) {
  if (position == leaves.size()) {
    DdNode* terminal =
        (truth & 1) ? Cudd_ReadOne(dd) : Cudd_ReadLogicZero(dd);
    Cudd_Ref(terminal);
    return terminal;
  }

  size_t remaining = leaves.size() - position - 1;
  uint64_t halfSize = 1ULL << remaining;
  uint64_t mask = (1ULL << halfSize) - 1;
  uint64_t lowTruth = truth & mask;
  uint64_t highTruth = (truth >> halfSize) & mask;

  DdNode* low = Lsv_BuildBdd(dd, leaves, lowTruth, position + 1);

  DdNode* high = Lsv_BuildBdd(dd, leaves, highTruth, position + 1);

  DdNode* variable = Cudd_bddIthVar(dd, leaves[position]);
  DdNode* result = Cudd_bddIte(dd, variable, high, low);
  Cudd_Ref(result);

  Cudd_RecursiveDeref(dd, low);
  Cudd_RecursiveDeref(dd, high);

  return result;
}

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

static int Lsv_CommandCutTruthTable(Abc_Frame_t* pAbc, int argc,
                                    char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

  if (argc != 2) {
    Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
    return 1;
  }

  int k = atoi(argv[1]);
  if (k < 2 || k > 6) {
    Abc_Print(-1, "k must be between 2 and 6.\n");
    return 1;
  }

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network must be transformed by strash first.\n");
    return 1;
  }

  std::vector<std::vector<LsvCut>> cuts(Abc_NtkObjNumMax(pNtk));
  Lsv_InitializeLeafCuts(pNtk, cuts);

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int nodeId = Abc_ObjId(pObj);

    LsvCut trivial;
    trivial.leaves.push_back(nodeId);
    trivial.truth = 0x2;

    cuts[nodeId].push_back(trivial);

    Abc_Obj_t* fanin0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* fanin1 = Abc_ObjFanin1(pObj);

    int fanin0Id = Abc_ObjId(fanin0);
    int fanin1Id = Abc_ObjId(fanin1);

    for (const LsvCut& cut0 : cuts[fanin0Id]) {
      for (const LsvCut& cut1 : cuts[fanin1Id]) {
        std::vector<int> merged;

        if (!Lsv_MergeLeaves(cut0.leaves, cut1.leaves, k, merged)) {
          continue;
        }

        if (Lsv_CutExists(cuts[nodeId], merged)) {
          continue;
        }

        LsvCut combined;
        combined.leaves = merged;
        combined.truth = 0;
        cuts[nodeId].push_back(combined);
      }
    }

    for (LsvCut& cut : cuts[nodeId]) {
      cut.truth = Lsv_ComputeTruth(
          pObj, cut.leaves, Abc_NtkObjNumMax(pNtk));

      printf("%d: ", nodeId);
      Lsv_PrintLeaves(cut.leaves);
      printf(": %llX\n",
             static_cast<unsigned long long>(cut.truth));
    }
  }

  return 0;

}

static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc,
                                 char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

  if (argc != 2) {
    Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
    return 1;
  }

  int k = atoi(argv[1]);
  if (k < 2 || k > 6) {
    Abc_Print(-1, "k must be between 2 and 6.\n");
    return 1;
  }

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network must be transformed by strash first.\n");
    return 1;
  }

  DdManager* dd = static_cast<DdManager*>(Abc_FrameReadManDd());
  std::vector<std::vector<LsvCut>> cuts(Abc_NtkObjNumMax(pNtk));
  Lsv_InitializeLeafCuts(pNtk, cuts);

  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachNode(pNtk, pObj, i) {
    int nodeId = Abc_ObjId(pObj);

    LsvCut trivial;
    trivial.leaves.push_back(nodeId);
    trivial.truth = 0x2;
    cuts[nodeId].push_back(trivial);

    Abc_Obj_t* fanin0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* fanin1 = Abc_ObjFanin1(pObj);

    int fanin0Id = Abc_ObjId(fanin0);
    int fanin1Id = Abc_ObjId(fanin1);

    for (const LsvCut& cut0 : cuts[fanin0Id]) {
      for (const LsvCut& cut1 : cuts[fanin1Id]) {
        std::vector<int> merged;

        if (!Lsv_MergeLeaves(cut0.leaves, cut1.leaves, k, merged)) {
          continue;
        }

        if (Lsv_CutExists(cuts[nodeId], merged)) {
          continue;
        }

        LsvCut combined;
        combined.leaves = merged;
        combined.truth = 0;
        cuts[nodeId].push_back(combined);
      }
    }

    for (LsvCut& cut : cuts[nodeId]) {
      cut.truth = Lsv_ComputeTruth(
          pObj, cut.leaves, Abc_NtkObjNumMax(pNtk));

      DdNode* bdd = Lsv_BuildBdd(dd, cut.leaves, cut.truth, 0);

      int bddSize = Cudd_DagSize(bdd);

      printf("%d: ", nodeId);
      Lsv_PrintLeaves(cut.leaves);
      printf(": %d\n", bddSize);

      Cudd_RecursiveDeref(dd, bdd);
    }
  }

  return 0;
}
