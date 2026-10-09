#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <cassert>
#include <cinttypes>
#include <cstdint>
#include <cstring>
#include <memory>
#include <set>
#include <unordered_map>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCuts(Abc_Frame_t* pAbc, int argc, char** argv);

using Cut = std::set<int>;
using CutCollection = std::set<Cut>;
enum class CutOutput { Leaves, TruthTable, BddSize };

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_enum", Lsv_CommandCuts, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCuts, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCuts, 0);
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

static bool Lsv_MergeCuts(const Cut& a, const Cut& b, int k, Cut& result) {
  if (a.size() > static_cast<size_t>(k) || b.size() > static_cast<size_t>(k))
    return false;
  result = a;
  for (int x : b) {
    result.insert(x);
    if (result.size() > static_cast<size_t>(k)) return false;
  }
  return true;
}

// Values correspond to cut leaves in ascending node-ID order.
// Caller supplies 0 <= assignment < 2^(cut.size()).
static std::vector<int> Lsv_CutInputValues(const Cut& cut, unsigned assignment) {
  const int m = static_cast<int>(cut.size());
  std::vector<int> values(m, 0);
  for (int j = 0; j < m; j++) {
    // The smallest leaf ID takes the most significant input bit.
    const int bitPosition = m - 1 - j;
    values[j] = (assignment >> bitPosition) & 1u;
  }
  return values;
}

// inputValues follows the same ascending leaf-ID order as cut.
static bool Lsv_EvaluateCut(Abc_Obj_t* pNode, const Cut& cut,
                           const std::vector<int>& inputValues,
                           std::unordered_map<int, bool>& memo) {
  assert(inputValues.size() == cut.size());
  const int id = Abc_ObjId(pNode);
  const auto cached = memo.find(id);
  if (cached != memo.end()) return cached->second;

  // Stop at cut leaves, including leaves that are internal AIG nodes.
  int j = 0;
  for (int leafId : cut) {
    if (id == leafId) return inputValues[j];
    j++;
  }

  if (Abc_AigNodeIsConst(pNode)) return true;
  assert(Abc_AigNodeIsAnd(pNode));

  bool aValue = Lsv_EvaluateCut(Abc_ObjFanin0(pNode), cut, inputValues, memo);
  bool bValue = Lsv_EvaluateCut(Abc_ObjFanin1(pNode), cut, inputValues, memo);
  const bool invertA = Abc_ObjFaninC0(pNode);
  const bool invertB = Abc_ObjFaninC1(pNode);

  if (invertA) {
    aValue = !aValue;
  }
  if (invertB) {
    bValue = !bValue;
  }
  const bool result = aValue && bValue;
  memo.emplace(id, result);
  return result;
}

static uint64_t Lsv_CutTruthTable(Abc_Obj_t* pRoot, const Cut& cut) {
  assert(cut.size() <= 6);
  const unsigned assignmentCount = 1u << cut.size();
  uint64_t truthTable = 0;
  std::unordered_map<int, bool> memo;
  for (unsigned assignment = 0; assignment < assignmentCount; assignment++) {
    // Values are valid only for this cut and this input assignment.
    memo.clear();
    const std::vector<int> inputValues = Lsv_CutInputValues(cut, assignment);
    const bool value = Lsv_EvaluateCut(pRoot, cut, inputValues, memo);
    if (value) {
      // Assignment 0 goes in the LSB; a six-leaf cut can use bit 63.
      truthTable |= uint64_t{1} << assignment;
    }
  }
  return truthTable;
}

// Returns a referenced BDD, or nullptr on failure.
// The manager must use index order without dynamic reordering.
// memo owns an additional reference to each cached internal-node result.
static DdNode* Lsv_BuildCutBdd(DdManager* dd, Abc_Obj_t* pNode, const Cut& cut,
                             std::unordered_map<int, DdNode*>& memo) {
  const int id = Abc_ObjId(pNode);
  const auto cached = memo.find(id);
  if (cached != memo.end()) {
    Cudd_Ref(cached->second);
    return cached->second;
  }
  int index = 0;
  for (int leafId : cut) {
    if (id == leafId) {
      DdNode* variable = Cudd_bddIthVar(dd, index);
      if (variable) Cudd_Ref(variable);
      return variable;
    }
    index++;
  }

  if (Abc_AigNodeIsConst(pNode)) {
    DdNode* one = Cudd_ReadOne(dd);
    Cudd_Ref(one);
    return one;
  }
  assert(Abc_AigNodeIsAnd(pNode));

  DdNode* a = Lsv_BuildCutBdd(dd, Abc_ObjFanin0(pNode), cut, memo);
  if (!a) return nullptr;
  DdNode* b = Lsv_BuildCutBdd(dd, Abc_ObjFanin1(pNode), cut, memo);
  if (!b) {
    Cudd_RecursiveDeref(dd, a);
    return nullptr;
  }

  const bool invertA = Abc_ObjFaninC0(pNode);
  const bool invertB = Abc_ObjFaninC1(pNode);
  if (invertA) {
    a = Cudd_Not(a);
  }
  if (invertB) {
    b = Cudd_Not(b);
  }
  DdNode* result = Cudd_bddAnd(dd, a, b);
  // Protect the result before releasing the child references (they may alias).
  if (result) Cudd_Ref(result);
  Cudd_RecursiveDeref(dd, a);
  Cudd_RecursiveDeref(dd, b);
  if (result) {
    Cudd_Ref(result);
    memo.emplace(id, result);
  }
  return result;
}

static int Lsv_CutBddSize(DdManager* dd, Abc_Obj_t* pRoot, const Cut& cut) {
  // AIG IDs have different variable meanings in different cuts: never reuse memo.
  std::unordered_map<int, DdNode*> memo;
  DdNode* root = Lsv_BuildCutBdd(dd, pRoot, cut, memo);
  const int size = root ? Cudd_DagSize(root) : -1;
  if (root) Cudd_RecursiveDeref(dd, root);
  for (const auto& entry : memo) {
    Cudd_RecursiveDeref(dd, entry.second);
  }
  return size;
}

static int Lsv_EnumerateCuts(Abc_Ntk_t* pNtk, int k, CutOutput output) {
  if (pNtk == nullptr) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network must be an AIG. Run strash first.\n");
    return 1;
  }
  if (k < 2 || k > 6) {
    Abc_Print(-1, "k must be between 2 and 6.\n");
    return 1;
  }

  // Reuse one manager, but release every cut's BDD references after counting.
  std::unique_ptr<DdManager, decltype(&Cudd_Quit)> dd(nullptr, &Cudd_Quit);
  if (output == CutOutput::BddSize) {
    dd.reset(Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0));
    if (!dd) {
      Abc_Print(-1, "Cannot initialize the CUDD manager.\n");
      return 1;
    }
    // Index 0 is the smallest cut leaf ID, so index order is the required order.
    Cudd_AutodynDisable(dd.get());
  }
  int n = Abc_NtkObjNumMax(pNtk);
  std::vector<CutCollection> cutsById(n);

  // Constants need no independent variable. Include latch outputs as boundaries
  // as well as PIs if a sequential network is supplied.
  cutsById[Abc_ObjId(Abc_AigConst1(pNtk))].insert(Cut{});
  Abc_Obj_t* pCi;
  int i;
  Abc_NtkForEachCi(pNtk, pCi, i) {
    const int id = Abc_ObjId(pCi);
    cutsById[id].insert(Cut{id});
  }

  // Collect all internal nodes in fanin-before-node order.
  Vec_Ptr_t* vNodes = Abc_NtkDfs(pNtk, 1);
  Abc_Obj_t* pNode;
  Vec_PtrForEachEntry(Abc_Obj_t*, vNodes, pNode, i) {
    const int id = Abc_ObjId(pNode);

    cutsById[id].insert(Cut{id});
    const int aId = Abc_ObjId(Abc_ObjFanin0(pNode));
    const int bId = Abc_ObjId(Abc_ObjFanin1(pNode));

    for (const Cut& a : cutsById[aId]) {
      for (const Cut& b : cutsById[bId]) {
        Cut result;
        if (Lsv_MergeCuts(a, b, k, result)) {
          cutsById[id].insert(result);
        }
      }
    }

    for (const Cut& cut : cutsById[id]) {
      int bddSize = 0;
      if (output == CutOutput::BddSize) {
        bddSize = Lsv_CutBddSize(dd.get(), pNode, cut);
        if (bddSize < 0) {
          Abc_Print(-1, "CUDD failed to construct a cut BDD.\n");
          Vec_PtrFree(vNodes);
          return 1;
        }
      }
      printf("%d:", id);
      for (int leafId : cut) {
        printf(" %d", leafId);
      }
      if (output == CutOutput::TruthTable) {
        const uint64_t truthTable = Lsv_CutTruthTable(pNode, cut);
        printf(": %" PRIX64, truthTable);
      } else if (output == CutOutput::BddSize) {
        printf(": %d", bddSize);
      }
      printf("\n");
    }
  }
  Vec_PtrFree(vNodes);
  assert(!dd || Cudd_CheckZeroRef(dd.get()) == 0);
  return 0;
}

// Shared argument handling for cut enumeration, truth tables, and BDD sizes.
static int Lsv_CommandCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  // Short-circuit evaluation checks argc before accessing argv[1].
  if (argc != 2 || argv[1][0] < '2' || argv[1][0] > '6' ||
      argv[1][1] != '\0') {
    Abc_Print(-2, "usage: %s <k> (2 <= k <= 6)\n", argv[0]);
    return 1;
  }

  const int k = argv[1][0] - '0';
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  CutOutput output = CutOutput::Leaves;
  if (std::strcmp(argv[0], "lsv_cut_tt") == 0) {
    output = CutOutput::TruthTable;
  } else if (std::strcmp(argv[0], "lsv_cut_bddsize") == 0) {
    output = CutOutput::BddSize;
  }

  return Lsv_EnumerateCuts(pNtk, k, output);
}