#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iterator>
#include <set>
#include <utility>
#include <vector>

namespace {

using Cut = std::vector<int>;
using CutList = std::vector<Cut>;

// ABC allocates AIG nodes after their fanins.  A PI is its own cut; the
// constant-one object has an empty cut; every AND has its unit cut plus
// the distinct unions of one cut from each fanin.
std::vector<CutList> EnumerateCuts(Abc_Ntk_t* ntk, int k) {
  std::vector<CutList> cuts(Abc_NtkObjNumMax(ntk));
  for (int id = 0; id < Abc_NtkObjNumMax(ntk); ++id) {
    Abc_Obj_t* obj = Abc_NtkObj(ntk, id);
    if (obj == nullptr) continue;
    if (obj->Type == ABC_OBJ_CONST1) {
      cuts[id].push_back(Cut());
    } else if (Abc_ObjIsCi(obj)) {
      cuts[id].push_back(Cut(1, id));
    } else if (Abc_ObjIsNode(obj)) {
      cuts[id].push_back(Cut(1, id));
      std::set<Cut> seen;
      seen.insert(cuts[id].front());
      const CutList& left = cuts[Abc_ObjFaninId0(obj)];
      const CutList& right = cuts[Abc_ObjFaninId1(obj)];
      for (const Cut& a : left) {
        for (const Cut& b : right) {
          Cut merged;
          std::set_union(a.begin(), a.end(), b.begin(), b.end(),
                         std::back_inserter(merged));
          if (static_cast<int>(merged.size()) <= k &&
              seen.insert(merged).second) {
            cuts[id].push_back(std::move(merged));
          }
        }
      }
    }
  }
  return cuts;
}

// Evaluate the logic cone, stopping at the cut leaves.  AIG inversions are
// edge attributes, so each fanin value is complemented at its parent.
int Evaluate(Abc_Ntk_t* ntk, int id, const Cut& cut, unsigned assignment,
             std::vector<std::int8_t>& memo) {
  auto leaf = std::lower_bound(cut.begin(), cut.end(), id);
  if (leaf != cut.end() && *leaf == id) {
    int position = static_cast<int>(leaf - cut.begin());
    return (assignment >> (cut.size() - 1 - position)) & 1U;
  }
  if (memo[id] != -2) return memo[id];
  Abc_Obj_t* obj = Abc_NtkObj(ntk, id);
  if (obj->Type == ABC_OBJ_CONST1) return memo[id] = 1;
  if (!Abc_ObjIsNode(obj)) return -1;
  int left = Evaluate(ntk, Abc_ObjFaninId0(obj), cut, assignment, memo);
  int right = Evaluate(ntk, Abc_ObjFaninId1(obj), cut, assignment, memo);
  if (left < 0 || right < 0) return -1;
  return memo[id] = ((left ^ Abc_ObjFaninC0(obj)) &
                     (right ^ Abc_ObjFaninC1(obj)));
}

bool TruthTable(Abc_Ntk_t* ntk, int root, const Cut& cut,
                std::uint64_t* result) {
  std::uint64_t table = 0;
  const unsigned assignments = 1U << cut.size();
  for (unsigned pattern = 0; pattern < assignments; ++pattern) {
    std::vector<std::int8_t> memo(Abc_NtkObjNumMax(ntk), -2);
    int value = Evaluate(ntk, root, cut, pattern, memo);
    if (value < 0) return false;
    if (value) table |= std::uint64_t{1} << pattern;
  }
  *result = table;
  return true;
}

// Construct a reduced ordered BDD by Shannon expansion of the truth table.
// Variable 0 corresponds to the smallest cut-node ID and is tested first.
// Each returned CUDD node has one reference owned by the caller.
DdNode* BuildBdd(DdManager* manager, std::uint64_t table, int level,
                 int count, unsigned first, unsigned length) {
  bool zero = true;
  bool one = true;
  for (unsigned i = first; i < first + length; ++i) {
    if ((table >> i) & 1U) zero = false;
    else one = false;
  }
  if (zero || one) {
    DdNode* constant = zero ? Cudd_ReadLogicZero(manager)
                            : Cudd_ReadOne(manager);
    Cudd_Ref(constant);
    return constant;
  }
  if (level == count) return nullptr;
  DdNode* low = BuildBdd(manager, table, level + 1, count, first,
                         length / 2);
  if (low == nullptr) return nullptr;
  DdNode* high = BuildBdd(manager, table, level + 1, count,
                          first + length / 2, length / 2);
  if (high == nullptr) {
    Cudd_RecursiveDeref(manager, low);
    return nullptr;
  }
  DdNode* result = Cudd_bddIte(manager, Cudd_bddIthVar(manager, level),
                               high, low);
  if (result != nullptr) Cudd_Ref(result);
  Cudd_RecursiveDeref(manager, low);
  Cudd_RecursiveDeref(manager, high);
  return result;
}

void PrintCut(int root, const Cut& cut) {
  std::printf("%d: ", root);
  for (std::size_t i = 0; i < cut.size(); ++i)
    std::printf("%s%d", i ? " " : "", cut[i]);
  std::printf(": ");
}

int RunCutCommand(Abc_Frame_t* frame, int argc, char** argv, bool bdd_size) {
  const char* name = bdd_size ? "lsv_cut_bddsize" : "lsv_cut_tt";
  if (argc != 2) {
    Abc_Print(-2, "usage: %s <k> (2 <= k <= 6)\n", name);
    return 1;
  }
  char* end = nullptr;
  long k = std::strtol(argv[1], &end, 10);
  if (*argv[1] == '\0' || *end != '\0' || k < 2 || k > 6) {
    Abc_Print(-2, "usage: %s <k> (2 <= k <= 6)\n", name);
    return 1;
  }
  Abc_Ntk_t* ntk = Abc_FrameReadNtk(frame);
  if (ntk == nullptr || !Abc_NtkIsStrash(ntk)) {
    Abc_Print(-1, "A structurally hashed AIG is required; run strash first.\n");
    return 1;
  }

  std::vector<CutList> cuts = EnumerateCuts(ntk, static_cast<int>(k));
  DdManager* manager = nullptr;
  if (bdd_size) {
    manager = Cudd_Init(static_cast<unsigned>(k), 0, CUDD_UNIQUE_SLOTS,
                        CUDD_CACHE_SLOTS, 0);
    if (manager == nullptr) {
      Abc_Print(-1, "Failed to initialize the BDD manager.\n");
      return 1;
    }
  }

  int status = 0;
  for (int id = 0; id < Abc_NtkObjNumMax(ntk) && status == 0; ++id) {
    Abc_Obj_t* obj = Abc_NtkObj(ntk, id);
    if (obj == nullptr || !Abc_ObjIsNode(obj)) continue;
    for (const Cut& cut : cuts[id]) {
      std::uint64_t table;
      if (!TruthTable(ntk, id, cut, &table)) {
        Abc_Print(-1, "Failed to evaluate a cut of node %d.\n", id);
        status = 1;
        break;
      }
      if (bdd_size) {
        DdNode* root = BuildBdd(manager, table, 0,
                                static_cast<int>(cut.size()), 0,
                                1U << cut.size());
        if (root == nullptr) {
          Abc_Print(-1, "Failed to build a BDD for node %d.\n", id);
          status = 1;
          break;
        }
        int size = Cudd_DagSize(root);
        Cudd_RecursiveDeref(manager, root);
        PrintCut(id, cut);
        std::printf("%d\n", size);
      } else {
        PrintCut(id, cut);
        std::printf("%llX\n", static_cast<unsigned long long>(table));
      }
    }
  }
  if (manager != nullptr) Cudd_Quit(manager);
  return status;
}

int CommandCutTruthTable(Abc_Frame_t* frame, int argc, char** argv) {
  return RunCutCommand(frame, argc, argv, false);
}

int CommandCutBddSize(Abc_Frame_t* frame, int argc, char** argv) {
  return RunCutCommand(frame, argc, argv, true);
}

}  // namespace

void Lsv_RegisterCutCommands(Abc_Frame_t* frame) {
  Cmd_CommandAdd(frame, "LSV", "lsv_cut_tt", CommandCutTruthTable, 0);
  Cmd_CommandAdd(frame, "LSV", "lsv_cut_bddsize", CommandCutBddSize, 0);
}
