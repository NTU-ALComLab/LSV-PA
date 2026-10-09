#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"
#endif

#include <cerrno>
#include <cinttypes>
#include <cstdlib>
#include <cstring>
#include <vector>

ABC_NAMESPACE_IMPL_START

namespace {

// Cuts have at most six leaves in this assignment. Leaves stay sorted by ID.
struct Cut {
  static constexpr int kMaxLeaves = 6;
  int leaves[kMaxLeaves];
  int size;

  Cut() : leaves{0}, size(0) {}
  explicit Cut(int id) : leaves{0}, size(1) { leaves[0] = id; }

  bool Equals(const Cut& other) const {
    if (size != other.size) return false;
    for (int i = 0; i < size; ++i)
      if (leaves[i] != other.leaves[i]) return false;
    return true;
  }

  // Form the sorted union, rejecting it if it would exceed the requested k.
  bool Merge(const Cut& other, int limit, Cut* result) const {
    result->size = 0;
    int left = 0;
    int right = 0;
    while (left < size || right < other.size) {
      int id;
      if (right == other.size ||
          (left < size && leaves[left] < other.leaves[right])) {
        id = leaves[left++];
      } else if (left == size || other.leaves[right] < leaves[left]) {
        id = other.leaves[right++];
      } else {
        id = leaves[left];
        ++left;
        ++right;
      }
      if (result->size == limit) return false;
      result->leaves[result->size++] = id;
    }
    return true;
  }
};

struct CutList {
  std::vector<Cut> cuts;

  void AddUnique(const Cut& candidate) {
    for (const Cut& cut : cuts)
      if (cut.Equals(candidate)) return;
    cuts.push_back(candidate);
  }
};

using NetworkCuts = std::vector<CutList>;

static int Lsv_Command(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);

// Dynamic programming in topological (object-ID) order. A CI has its trivial
// cut, and an AND's non-trivial cuts are unions of one cut from each fanin.
NetworkCuts Lsv_EnumerateCuts(Abc_Ntk_t* pNtk, int k) {
  NetworkCuts cuts(Abc_NtkObjNumMax(pNtk));

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachCi(pNtk, pObj, i) {
    cuts[Abc_ObjId(pObj)].AddUnique(Cut(Abc_ObjId(pObj)));
  }

  // This lets constants disappear when merged with another fanin cut.
  Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
  cuts[Abc_ObjId(pConst)].AddUnique(Cut());

  Abc_NtkForEachNode(pNtk, pObj, i) {
    CutList& node_cuts = cuts[Abc_ObjId(pObj)];
    node_cuts.AddUnique(Cut(Abc_ObjId(pObj)));  // The trivial cut.

    const CutList& first_cuts = cuts[Abc_ObjFaninId0(pObj)];
    const CutList& second_cuts = cuts[Abc_ObjFaninId1(pObj)];
    for (const Cut& first : first_cuts.cuts) {
      for (const Cut& second : second_cuts.cuts) {
        Cut merged;
        if (first.Merge(second, k, &merged)) node_cuts.AddUnique(merged);
      }
    }
  }
  return cuts;
}

uint64_t Lsv_VariableTruth(int variable, int variable_count) {
  const unsigned assignment_count = 1u << variable_count;
  const unsigned assignment_bit = variable_count - 1 - variable;
  uint64_t truth = 0;
  for (unsigned assignment = 0; assignment < assignment_count; ++assignment) {
    if ((assignment >> assignment_bit) & 1u)
      truth |= UINT64_C(1) << assignment;
  }
  return truth;
}

uint64_t Lsv_TruthRec(Abc_Obj_t* pObj, const std::vector<int>& leaf_position,
                      int variable_count, uint64_t mask,
                      std::vector<uint64_t>* memo,
                      std::vector<unsigned char>* computed) {
  const int id = Abc_ObjId(pObj);
  if ((*computed)[id]) return (*memo)[id];

  uint64_t result;
  if (leaf_position[id] >= 0) {
    result = Lsv_VariableTruth(leaf_position[id], variable_count);
  } else if (Abc_AigNodeIsConst(pObj)) {
    result = mask;
  } else {
    uint64_t first = Lsv_TruthRec(Abc_ObjFanin0(pObj), leaf_position,
                                  variable_count, mask, memo, computed);
    uint64_t second = Lsv_TruthRec(Abc_ObjFanin1(pObj), leaf_position,
                                   variable_count, mask, memo, computed);
    if (Abc_ObjFaninC0(pObj)) first = (~first) & mask;
    if (Abc_ObjFaninC1(pObj)) second = (~second) & mask;
    result = first & second;
  }
  (*computed)[id] = 1;
  (*memo)[id] = result;
  return result;
}

uint64_t Lsv_CutTruth(Abc_Ntk_t* pNtk, Abc_Obj_t* pRoot, const Cut& cut) {
  const int object_count = Abc_NtkObjNumMax(pNtk);
  std::vector<int> leaf_position(object_count, -1);
  for (int i = 0; i < cut.size; ++i)
    leaf_position[cut.leaves[i]] = i;

  const unsigned bit_count = 1u << cut.size;
  const uint64_t mask = bit_count == 64
                            ? UINT64_MAX
                            : (UINT64_C(1) << bit_count) - UINT64_C(1);
  std::vector<uint64_t> memo(object_count, 0);
  std::vector<unsigned char> computed(object_count, 0);
  return Lsv_TruthRec(pRoot, leaf_position, cut.size, mask, &memo,
                      &computed) & mask;
}

void Lsv_PrintPrefix(int root_id, const Cut& cut) {
  Abc_Print(1, "%d:", root_id);
  for (int i = 0; i < cut.size; ++i) Abc_Print(1, " %d", cut.leaves[i]);
  Abc_Print(1, ": ");
}

void Lsv_PrintTruthTables(Abc_Ntk_t* pNtk, const NetworkCuts& cuts) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const Cut& cut : cuts[Abc_ObjId(pObj)].cuts) {
      Lsv_PrintPrefix(Abc_ObjId(pObj), cut);
      Abc_Print(1, "%" PRIX64 "\n", Lsv_CutTruth(pNtk, pObj, cut));
    }
  }
}

#ifdef ABC_USE_CUDD
DdNode* Lsv_BddRec(Abc_Obj_t* pObj, DdManager* manager,
                   const std::vector<int>& leaf_position,
                   std::vector<DdNode*>* memo) {
  const int id = Abc_ObjId(pObj);
  if ((*memo)[id] != nullptr) return (*memo)[id];

  DdNode* result;
  if (leaf_position[id] >= 0) {
    result = Cudd_bddIthVar(manager, leaf_position[id]);
  } else if (Abc_AigNodeIsConst(pObj)) {
    result = Cudd_ReadOne(manager);
  } else {
    DdNode* first = Lsv_BddRec(Abc_ObjFanin0(pObj), manager,
                               leaf_position, memo);
    DdNode* second = Lsv_BddRec(Abc_ObjFanin1(pObj), manager,
                                leaf_position, memo);
    if (first == nullptr || second == nullptr) return nullptr;
    first = Cudd_NotCond(first, Abc_ObjFaninC0(pObj));
    second = Cudd_NotCond(second, Abc_ObjFaninC1(pObj));
    result = Cudd_bddAnd(manager, first, second);
    if (result == nullptr) return nullptr;
  }
  Cudd_Ref(result);
  (*memo)[id] = result;
  return result;
}

int Lsv_CutBddSize(Abc_Ntk_t* pNtk, Abc_Obj_t* pRoot, const Cut& cut,
                   DdManager* manager) {
  const int object_count = Abc_NtkObjNumMax(pNtk);
  std::vector<int> leaf_position(object_count, -1);
  for (int i = 0; i < cut.size; ++i)
    leaf_position[cut.leaves[i]] = i;
  std::vector<DdNode*> memo(object_count, nullptr);

  DdNode* root = Lsv_BddRec(pRoot, manager, leaf_position, &memo);
  const int size = root == nullptr ? -1 : Cudd_DagSize(root);
  for (DdNode* node : memo)
    if (node != nullptr) Cudd_RecursiveDeref(manager, node);
  return size;
}

bool Lsv_PrintBddSizes(Abc_Ntk_t* pNtk, const NetworkCuts& cuts, int k) {
  // Variables 0..k-1 always follow the sorted leaf order. Reusing one manager
  // avoids paying CUDD's initialization cost once for every cut.
  DdManager* manager =
      Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  if (manager == nullptr) return false;

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    for (const Cut& cut : cuts[Abc_ObjId(pObj)].cuts) {
      Lsv_PrintPrefix(Abc_ObjId(pObj), cut);
      Abc_Print(1, "%d\n", Lsv_CutBddSize(pNtk, pObj, cut, manager));
    }
  }
  Cudd_Quit(manager);
  return true;
}
#endif

bool Lsv_ParseK(const char* text, int* k) {
  char* end = nullptr;
  errno = 0;
  const long value = std::strtol(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0' || value < 2 || value > 6)
    return false;
  *k = static_cast<int>(value);
  return true;
}

void Lsv_PrintUsage() {
  Abc_Print(-2, "usage: lsv cut <tt|bddsize> <k>\n");
  Abc_Print(-2, "       k must be between 2 and 6\n");
}

int Lsv_Command(Abc_Frame_t* pAbc, int argc, char** argv) {
  if (argc != 4 || std::strcmp(argv[1], "cut") != 0 ||
      (std::strcmp(argv[2], "tt") != 0 &&
       std::strcmp(argv[2], "bddsize") != 0)) {
    Lsv_PrintUsage();
    return 1;
  }

  int k;
  if (!Lsv_ParseK(argv[3], &k)) {
    Lsv_PrintUsage();
    return 1;
  }

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (pNtk == nullptr) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(
        -1,
        "The network must be a structurally hashed AIG. Run strash first.\n");
    return 1;
  }

  const NetworkCuts cuts = Lsv_EnumerateCuts(pNtk, k);
  if (std::strcmp(argv[2], "tt") == 0) {
    Lsv_PrintTruthTables(pNtk, cuts);
    return 0;
  }

#ifdef ABC_USE_CUDD
  if (!Lsv_PrintBddSizes(pNtk, cuts, k)) {
    Abc_Print(-1, "Could not initialize the CUDD manager.\n");
    return 1;
  }
  return 0;
#else
  Abc_Print(-1,
            "BDD support is unavailable because ABC was built without CUDD.\n");
  return 1;
#endif
}

// Accept underscore names without requiring aliases in abc.rc.
int Lsv_CommandCutAlias(Abc_Frame_t* pAbc, int argc, char** argv) {
  if (argc != 2) {
    Abc_Print(-2, "usage: %s <k>\n", argv[0]);
    return 1;
  }
  char cut[] = "cut";
  char tt[] = "tt";
  char bddsize[] = "bddsize";
  char* mode = std::strcmp(argv[0], "lsv_cut_tt") == 0 ? tt : bddsize;
  char* arguments[] = {argv[0], cut, mode, argv[1]};
  return Lsv_Command(pAbc, 4, arguments);
}

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

void Lsv_Init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv", Lsv_Command, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutAlias, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutAlias, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
}

void Lsv_Destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {Lsv_Init, Lsv_Destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

}  // namespace

ABC_NAMESPACE_IMPL_END
