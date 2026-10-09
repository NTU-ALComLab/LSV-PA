#include "base/abc/abc.h"
#include "base/main/main.h"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

using std::vector;

typedef vector<int> Lsv_Cut;
typedef vector<Lsv_Cut> Lsv_CutList;
typedef vector<Lsv_CutList> Lsv_AllCuts;

static bool Lsv_CutEqual(const Lsv_Cut& a, const Lsv_Cut& b) {
  return a == b;
}

static void Lsv_AddUniqueCut(Lsv_CutList& cuts, Lsv_Cut cut) {
  std::sort(cut.begin(), cut.end());

  for (const Lsv_Cut& oldCut : cuts) {
    if (Lsv_CutEqual(oldCut, cut)) {
      return;
    }
  }

  cuts.push_back(cut);
}

static Lsv_Cut Lsv_MergeCuts(const Lsv_Cut& a, const Lsv_Cut& b) {
  Lsv_Cut result;
  result.reserve(a.size() + b.size());

  std::set_union(a.begin(), a.end(),
                 b.begin(), b.end(),
                 std::back_inserter(result));

  return result;
}

/*
 * Recursively computes all cuts rooted at pObj.

 * For a primary input:
 *     cuts = {{PI_ID}}
 *
 * For the AIG constant-one node:
 *     cuts = {{}}
 *
 * For an internal AND node:
 *     cuts = {{node_ID}} union
 *            { merge(cut0, cut1) |
 *              cut0 in cuts(fanin0),
 *              cut1 in cuts(fanin1),
 *              |merge(cut0, cut1)| <= k }
 */
static const Lsv_CutList& Lsv_ComputeCuts(
    Abc_Obj_t* pObj,
    int k,
    Lsv_AllCuts& allCuts,
    vector<char>& computed) {
  Abc_Obj_t* pRegular = Abc_ObjRegular(pObj);
  int id = Abc_ObjId(pRegular);

  if (computed[id]) {
    return allCuts[id];
  }

  computed[id] = 1;
  Lsv_CutList& cuts = allCuts[id];

  if (Abc_AigNodeIsConst(pRegular)) {
    // The constant-one node has an empty support.
    cuts.push_back(Lsv_Cut());
    return cuts;
  }

  if (Abc_ObjIsPi(pRegular)) {
    cuts.push_back(Lsv_Cut(1, id));
    return cuts;
  }

  if (!Abc_ObjIsNode(pRegular)) {
    // This should not occur after strash for ordinary combinational AIGs.
    // Treat the object as a leaf to avoid crashing on unusual input.
    cuts.push_back(Lsv_Cut(1, id));
    return cuts;
  }

  // Every internal node has a trivial cut containing only itself.
  cuts.push_back(Lsv_Cut(1, id));

  if (Abc_ObjFaninNum(pRegular) != 2) {
    return cuts;
  }

  Abc_Obj_t* pFanin0 = Abc_ObjFanin(pRegular, 0);
  Abc_Obj_t* pFanin1 = Abc_ObjFanin(pRegular, 1);

  const Lsv_CutList& cuts0 =
      Lsv_ComputeCuts(pFanin0, k, allCuts, computed);
  const Lsv_CutList& cuts1 =
      Lsv_ComputeCuts(pFanin1, k, allCuts, computed);

  for (const Lsv_Cut& cut0 : cuts0) {
  for (const Lsv_Cut& cut1 : cuts1) {
    Lsv_Cut merged = Lsv_MergeCuts(cut0, cut1);

    /*
     * The current root may only occur in its trivial cut {id}.
     * It must not occur in a merged child cut.
     */
    if (std::binary_search(
            merged.begin(),
            merged.end(),
            id)) {
      continue;
    }

    if (static_cast<int>(merged.size()) <= k) {
      Lsv_AddUniqueCut(cuts, merged);
    }
  }
}

  // Deterministic output order.
  std::sort(cuts.begin(), cuts.end(),
            [](const Lsv_Cut& a, const Lsv_Cut& b) {
              if (a.size() != b.size()) {
                return a.size() < b.size();
              }
              return a < b;
            });

  return cuts;
}

static int Lsv_FindCutVariable(
    const Lsv_Cut& cut,
    int nodeId) {
  auto it = std::lower_bound(cut.begin(), cut.end(), nodeId);

  if (it == cut.end() || *it != nodeId) {
    return -1;
  }

  return static_cast<int>(it - cut.begin());
}

static unsigned Lsv_EvalNode(
    Abc_Obj_t* pNode,
    uint64_t assignment,
    const Lsv_Cut& cut);

static unsigned Lsv_EvalLiteral(
    Abc_Obj_t* pLiteral,
    uint64_t assignment,
    const Lsv_Cut& cut) {
  Abc_Obj_t* pRegular = Abc_ObjRegular(pLiteral);

  unsigned value =
      Lsv_EvalNode(pRegular, assignment, cut);

  if (Abc_ObjIsComplement(pLiteral)) {
    value ^= 1U;
  }

  return value;
}

static unsigned Lsv_EvalNode(
    Abc_Obj_t* pNode,
    uint64_t assignment,
    const Lsv_Cut& cut) {
  Abc_Obj_t* pRegular = Abc_ObjRegular(pNode);
  int nodeId = Abc_ObjId(pRegular);

  /*
   * This test must happen before checking whether the object
   * is a PI, node, or constant.
   */
  int varIndex = Lsv_FindCutVariable(cut, nodeId);

  if (varIndex >= 0) {
    return static_cast<unsigned>(
        (assignment >> varIndex) & 1ULL);
  }

  if (Abc_AigNodeIsConst(pRegular)) {
    return 1;
  }

  if (Abc_ObjIsNode(pRegular)) {
    Abc_Obj_t* pFanin0 = Abc_ObjFanin(pRegular, 0);
    Abc_Obj_t* pFanin1 = Abc_ObjFanin(pRegular, 1);

    unsigned value0 =
        Lsv_EvalLiteral(pFanin0, assignment, cut);

    unsigned value1 =
        Lsv_EvalLiteral(pFanin1, assignment, cut);

    return value0 & value1;
  }

  /*
   * A primary input should normally appear in the cut.
   * Returning zero here makes malformed cuts obvious.
   */
  if (Abc_ObjIsPi(pRegular)) {
    Abc_Print(
        -1,
        "Error: PI %d is not present in the cut.\n",
        nodeId);
    return 0;
  }

  return 0;
}

static uint64_t Lsv_CutTruthTable(
    Abc_Obj_t* pRoot,
    const Lsv_Cut& cut) {
  uint64_t truthTable = 0;
  uint64_t nAssignments = 1ULL << cut.size();

  for (uint64_t assignment = 0;
       assignment < nAssignments;
       ++assignment) {
    unsigned value =
        Lsv_EvalNode(pRoot, assignment, cut);

    if (value) {
      truthTable |= 1ULL << assignment;
    }
  }

  return truthTable;
}

int Lsv_CutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

  if (pNtk == nullptr) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The current network is not an AIG. Run strash first.\n");
    return 1;
  }

  if (argc != 2 ||
      argv[1] == nullptr ||
      argv[1][0] == '-') {
    Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
    Abc_Print(-2, "\tEnumerate all k-feasible cuts of AIG nodes.\n");
    return 1;
  }

  char* end = nullptr;
  long kLong = std::strtol(argv[1], &end, 10);

  if (end == argv[1] ||
      *end != '\0' ||
      kLong < 1 ||
      kLong > 6) {
    Abc_Print(-1, "Error: k must be an integer in the range 1..6.\n");
    return 1;
  }

  int k = static_cast<int>(kLong);

  const int maxObjectId = Abc_NtkObjNumMax(pNtk);

  Lsv_AllCuts allCuts(maxObjectId);
  vector<char> computed(maxObjectId, 0);

  Abc_Obj_t* pNode;
  int i;

  /*
   * Abc_NtkForEachNode visits internal AIG nodes only, so primary
   * inputs and primary outputs are not printed.
   */
  Abc_NtkForEachNode(pNtk, pNode, i) {
    const Lsv_CutList& cuts =
        Lsv_ComputeCuts(pNode, k, allCuts, computed);

    for (const Lsv_Cut& cut : cuts) {
      uint64_t truthTable =
          Lsv_CutTruthTable(pNode, cut);

      std::printf("%d:", Abc_ObjId(pNode));

      for (int leafId : cut) {
        std::printf(" %d", leafId);
      }

      std::printf(": %llX\n",
                  static_cast<unsigned long long>(truthTable));
    }
  }

  return 0;
}
