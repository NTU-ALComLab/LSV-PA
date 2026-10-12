#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <cstdint>
#include <utility>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandDumpAig(Abc_Frame_t* pAbc, int argc, char** argv);


void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_dump_aig", Lsv_CommandDumpAig, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = { init, destroy };

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

///////////////////////////////
////////// Start PA1 //////////
////////// Start 4.1 //////////
///////////////////////////////

// make command:
// make ABC_USE_STDINT_H=1 -j$(nproc)

// A k-feasible cut is represented as a sorted (ascending by node ID) list of
// leaf node IDs. Sorting is required both for cheap dominance/duplicate
// checks (two-pointer) and for deterministic truth-table bit.
// Ordering (smallest ID = MSB, see Lsv_ComputeCutTruthTable).
struct Lsv_Cut_t {
  std::vector<int> leaves; // list of node IDs
};


// Merge two sorted, duplicate-free leaf lists (cuts of the two fan-ins) into
// a single sorted, duplicate-free leaf list. Returns false (and leaves
// outMerged's contents unspecified/partial) as soon as the merged size would
// exceed k.
//
// Standard sorted-merge with dedup: at each step we compare the fronts of
// both lists, take the smaller one (or either, if equal, and advance both
// pointers to skip the duplicate), and append it to the result.
static bool Lsv_MergeCuts(const std::vector<int>& leavesA,
  const std::vector<int>& leavesB, int k,
  std::vector<int>& outMerged) {
  outMerged.clear(); // out put vector, it is cleared at the start
  outMerged.reserve(leavesA.size() + leavesB.size());

  size_t i = 0, j = 0;
  while (i < leavesA.size() || j < leavesB.size()) {
    int nextVal;
    if (i >= leavesA.size()) { // A is exhausted, take from B.
      nextVal = leavesB[j++];
    }
    else if (j >= leavesB.size()) { // B is exhausted, take from A.
      nextVal = leavesA[i++];
    }
    else if (leavesA[i] < leavesB[j]) { // A's front is smaller, take it.
      nextVal = leavesA[i++];
    }
    else if (leavesB[j] < leavesA[i]) { // B's front is smaller, take it.
      nextVal = leavesB[j++];
    }
    else {
      // Equal: same leaf appears in both cuts, only keep one copy.
      nextVal = leavesA[i];
      ++i;
      ++j;
    }

    if (static_cast<int>(outMerged.size()) >= k) { // exceeded k-feasibility limit
      return false;
    }
    outMerged.push_back(nextVal); // no violation, append to result and continue
  }
  return true;
}


// Returns true if `smaller` is a subset of `bigger`. Both must be sorted
// ascending. Classic two-pointer subset test: walk both lists together;
// every element of `smaller` must be found in `bigger` along the way.
static bool Lsv_IsCutSubset(const std::vector<int>& smaller,
  const std::vector<int>& bigger) {
  if (smaller.size() > bigger.size())
    return false;

  size_t i = 0, j = 0;
  while (i < smaller.size() && j < bigger.size()) {
    if (smaller[i] == bigger[j]) {
      ++i;
      ++j;
    }
    else if (bigger[j] < smaller[i]) {
      ++j;
    }
    else {
      // bigger[j] > smaller[i]: smaller[i] can never be matched now.
      return false;
    }
  }
  // Success only if we matched every element of `smaller`.
  return i == smaller.size();
}


// Attempt to add a newly-formed cut (given by its sorted leaf list) into
// cutList, applying dedup + dominance filtering
// pseudocode:
//   - If any existing cut is a subset of (or equal to) newLeaves, newLeaves
//     is dominated/duplicate -> discard it entirely.
//   - Otherwise, remove any existing cut that newLeaves dominates (i.e.
//     newLeaves is a subset of it), then append newLeaves.
// Appending at the end (rather than inserting in sorted position) preserves
// the generation order required by the assignment; the TA has confirmed
// cut order doesn't affect grading, but we keep this for
// consistency with the worked example.
static void Lsv_TryAddCut(std::vector<Lsv_Cut_t>& cutList,
  const std::vector<int>& newLeaves) {
  for (const Lsv_Cut_t& existingCut : cutList) {
    if (Lsv_IsCutSubset(existingCut.leaves, newLeaves)) {
      // newLeaves is dominated by (or identical to) an existing cut.
      return;
    }
  }

  // Remove existing cuts that newLeaves dominates.
  cutList.erase(
    std::remove_if(cutList.begin(), cutList.end(),
      [&newLeaves](const Lsv_Cut_t& existingCut) {
        return Lsv_IsCutSubset(newLeaves, existingCut.leaves);
      }),
    cutList.end());

  Lsv_Cut_t newCut;
  newCut.leaves = newLeaves;
  cutList.push_back(std::move(newCut));
}


// Enumerate all k-feasible cuts for every node in the AIG.
//
// outCuts is indexed by Abc_ObjId(node); outCuts[id] = Phi(node), the list
// of k-feasible cuts rooted at that node. Caller is responsible for sizing
// nothing in advance -- this function resizes outCuts itself based on
// Abc_NtkObjNumMax(pNtk).
//
// Per the assignment's pseudocode:
//   - Every CI (primary input) gets only its trivial cut {itself}.
//   - Every internal AND node gets: its trivial cut {itself}, plus every
//     valid (size <= k, non-dominated) merge of a cut from fanin0's Phi
//     with a cut from fanin1's Phi.
//   - AND nodes are processed in increasing node-ID order, which for a
//     structurally-hashed (strashed) AIG is guaranteed to be a topological
//     order (a node's ID is always greater than both its fanins' IDs), so
//     Abc_AigForEachAnd's natural iteration order is safe to use directly.
static void Lsv_EnumerateKFeasibleCuts(Abc_Ntk_t* pNtk, int k,
  std::vector<std::vector<Lsv_Cut_t>>& outCuts) {
  // Resize outCuts, vector<Lsv_Cut_t> is 2D vector
  outCuts.assign(Abc_NtkObjNumMax(pNtk) + 1, std::vector<Lsv_Cut_t>());

  // Step 1: every primary input gets only the trivial cut.
  Abc_Obj_t* pCiObj;
  int ciIndex;
  Abc_NtkForEachCi(pNtk, pCiObj, ciIndex) {
    int id = Abc_ObjId(pCiObj);
    Lsv_Cut_t trivialCut;
    trivialCut.leaves.push_back(id);
    outCuts[id].push_back(std::move(trivialCut));
  }

  // Step 2: process internal AND nodes in topological (increasing ID) order.
  Abc_Obj_t* pNode;
  int nodeIndex;
  Abc_AigForEachAnd(pNtk, pNode, nodeIndex) {
    int id = Abc_ObjId(pNode);

    // Trivial cut {node itself} always comes first.
    Lsv_Cut_t trivialCut;
    trivialCut.leaves.push_back(id);
    outCuts[id].push_back(std::move(trivialCut));

    Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pNode);
    Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pNode);
    const std::vector<Lsv_Cut_t>& fanin0Cuts = outCuts[Abc_ObjId(pFanin0)];
    const std::vector<Lsv_Cut_t>& fanin1Cuts = outCuts[Abc_ObjId(pFanin1)];

    // Outer loop over fanin0's cuts, inner loop over fanin1's cuts, matching
    // the order specified in the assignment's pseudocode.
    std::vector<int> mergedLeaves;
    for (const Lsv_Cut_t& cutA : fanin0Cuts) {
      for (const Lsv_Cut_t& cutB : fanin1Cuts) {
        if (!Lsv_MergeCuts(cutA.leaves, cutB.leaves, k, mergedLeaves)) {
          // Merged cut would exceed k leaves -- discard.
          continue;
        }
        Lsv_TryAddCut(outCuts[id], mergedLeaves);
      }
    }
  }
}


// Evaluate the AIG cone rooted at pObj for ONE particular INPUT ASSIGNMENT
// (eg: 00101101), given a mapping from leaf node ID -> bit position within
// the cut. Uses a stamp-based memo so that shared sub-cones are only evaluated
// once per assignment, without needing to clear the whole array per assignment.
//
// Correctly handles inverted fanin edges (Abc_ObjFaninC0/1) and the
// constant-1 node.
static int Lsv_EvalCutAtAssignment(
  Abc_Obj_t* pObj, const std::unordered_map<int, int>& leafBitPos,
  int assignment, int numLeaves, std::vector<int>& stampArr,
  std::vector<int>& valArr, int stampCounter) {
  int id = Abc_ObjId(pObj);

  // Base case 1: pObj is one of the cut's leaves. Its value comes directly
  // from the input assignment bits, not from recursing further.
  auto leafIt = leafBitPos.find(id);
  if (leafIt != leafBitPos.end()) {
    // Leaf at sorted position p (p = 0 -> smallest node ID) corresponds to
    // bit weight (numLeaves - 1 - p): smallest ID = MSB of the index.
    int bitWeight = numLeaves - 1 - leafIt->second;
    return (assignment >> bitWeight) & 1;
  }

  // Base case 2: constant-1 node (not expected in this assignment's test
  // circuits, but handled defensively).
  if (Abc_AigNodeIsConst(pObj)) {
    return 1;
  }

  // Memoized case: pObj already evaluated for this assignment.
  if (stampArr[id] == stampCounter) {
    return valArr[id];
  }

  // Recursive case: pObj is an internal AND node inside the cut's cone but
  // not itself a leaf. Evaluate both fanins (respecting inverted edges)
  // and AND them together.
  int fanin0Val = Lsv_EvalCutAtAssignment(Abc_ObjFanin0(pObj), leafBitPos,
    assignment, numLeaves, stampArr,
    valArr, stampCounter) ^
    Abc_ObjFaninC0(pObj);   // XOR with the inversion flag
  int fanin1Val = Lsv_EvalCutAtAssignment(Abc_ObjFanin1(pObj), leafBitPos,
    assignment, numLeaves, stampArr,
    valArr, stampCounter) ^
    Abc_ObjFaninC1(pObj);   // XOR with the inversion flag
  int result = fanin0Val & fanin1Val; // AND the two fanin values

  stampArr[id] = stampCounter;
  valArr[id] = result;
  return result;
}


// Compute the truth table of a single cut rooted at pRoot, with the given
// leaves (must be sorted ascending). Evaluates ALL 2^|leaves| input
// ASSIGNMENTS in binary counting order; assignment 0 (00...0) maps to bit 0
// (LSB) of the result, assignment (2^|leaves| - 1) (11...1) maps to the
// highest bit used.
//
// |leaves| is expected to be in [1, 6] for this assignment's test cases
// (k in [2,6]; a trivial cut has exactly 1 leaf), so the result always fits
// comfortably in a uint64_t.
static uint64_t Lsv_ComputeCutTruthTable(Abc_Ntk_t* pNtk, Abc_Obj_t* pRoot,
  const std::vector<int>& leaves) {
  int numLeaves = static_cast<int>(leaves.size());

  // Map each leaf's node ID to its position within the sorted leaf list.
  std::unordered_map<int, int> leafBitPos;
  for (int pos = 0; pos < numLeaves; ++pos) {
    leafBitPos[leaves[pos]] = pos;
  }

  // Stamp-based memo, sized for any valid node ID in this network. A
  // monotonically increasing stamp per assignment lets us treat the memo as
  // "cleared" in O(1) rather than re-zeroing the whole array for every one
  // of the (up to 64) assignments.
  std::vector<int> stampArr(Abc_NtkObjNumMax(pNtk) + 1, 0);
  std::vector<int> valArr(Abc_NtkObjNumMax(pNtk) + 1, 0);
  int stampCounter = 0;

  uint64_t truthTable = 0;
  int numAssignments = 1 << numLeaves;

  // Enumerate all 2^|leaves| input assignments in binary counting order
  for (int assignment = 0; assignment < numAssignments; ++assignment) {
    ++stampCounter;
    int bitValue = Lsv_EvalCutAtAssignment(pRoot, leafBitPos, assignment,
      numLeaves, stampArr, valArr,
      stampCounter);
    if (bitValue) {
      truthTable |= (static_cast<uint64_t>(1) << assignment);
    }
  }
  return truthTable;
}


// Top-level driver for the "lsv_cut_tt" command: enumerate all k-feasible
// cuts of every internal AND node in the AIG, compute each cut's truth
// table, and print the results in the format required by the assignment.
//
// Per the assignment spec, cuts rooted at primary inputs/outputs are not
// printed (only cuts rooted at internal AND nodes), and node IDs within a
// cut are printed in ascending order (which Lsv_Cut_t::leaves already
// maintains).
static void Lsv_PrintCutTruthTables(Abc_Ntk_t* pNtk, int k) {
  std::vector<std::vector<Lsv_Cut_t>> allCuts;
  // Enumerate all k-feasible cuts for every node in the AIG, storing them
  Lsv_EnumerateKFeasibleCuts(pNtk, k, allCuts);

  // Print in increasing node-ID order (i.e. the same order
  // Abc_AigForEachAnd walks the network), and within each node, in the
  // order cuts were generated (trivial cut first, per Lsv_TryAddCut's
  // append-only behavior). The TA has confirmed cut order does not affect
  // grading, but this keeps output consistent with the assignment's
  // worked example.
  Abc_Obj_t* pNode;
  int nodeIndex;
  Abc_AigForEachAnd(pNtk, pNode, nodeIndex) {
    int id = Abc_ObjId(pNode);
    for (const Lsv_Cut_t& cut : allCuts[id]) {
      uint64_t truthTable = Lsv_ComputeCutTruthTable(pNtk, pNode, cut.leaves);

      printf("%d: ", id);
      for (size_t leafIdx = 0; leafIdx < cut.leaves.size(); ++leafIdx) {
        if (leafIdx > 0)
          printf(" ");
        printf("%d", cut.leaves[leafIdx]);
      }
      // Hexadecimal, uppercase, no leading zeros -- matches assignment's
      // example output (e.g. "2A", "8", "30").
      printf(": %llX\n", static_cast<unsigned long long>(truthTable));
    }
  }
}

// Parse command line
int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Expecting an AIG (run \"strash\" first).\n");
    return 1;
  }
  // Expect exactly one positional argument: <k>.
  if (argc != globalUtilOptind + 1) {
    goto usage;
  }

  {
    int k = atoi(argv[globalUtilOptind]);
    if (k < 1) {
      Abc_Print(-1, "Invalid k = %d: k must be >= 1.\n", k);
      return 1;
    }
    if (k > 6) {
      Abc_Print(0, "Warning: k = %d exceeds the expected range (2-6); proceeding anyway.\n", k);
    }
    Lsv_PrintCutTruthTables(pNtk, k);
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt [-h] <k>\n");
  Abc_Print(-2, "\t        enumerate k-feasible cuts and print their truth tables\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

///////////////////////////////
//////////  End  4.1 //////////
////////// Start 4.2 //////////
///////////////////////////////


// Recursively build the BDD with a Bottom-Up approach, starting from the leaves.
// The leaves are BDD with only ONE variable (base case). 
// The internal nodes are built by ANDing the BDDs of the fan-ins, and applying complement for inverted edges.
// ANDing is done using Cudd_bddAnd, BDD decision order is determined by the node ID.
//
// memo caches one Cudd_Ref'd DdNode* per node ID already built within this
// cut's cone , so shared sub-cones are only built once. Every stored node is
// Ref'd exactly once at the point it's first computed.
static DdNode* Lsv_BuildCutBdd(
  DdManager* dd, Abc_Obj_t* pObj,
  const std::unordered_map<int, int>& leafVarIndex,
  std::unordered_map<int, DdNode*>& memo) {
  int id = Abc_ObjId(pObj);

  // Already built (covers repeated visits to shared leaves/sub-cones).
  auto memoIt = memo.find(id);
  if (memoIt != memo.end()) {
    return memoIt->second;
  }

  DdNode* result;

  auto leafIt = leafVarIndex.find(id);
  if (leafIt != leafVarIndex.end()) {
    // Base case: pObj is one of the cut's leaves
    result = Cudd_bddIthVar(dd, leafIt->second); // create a BDD variable for this leaf 
    Cudd_Ref(result); 
  }
  else if (Abc_AigNodeIsConst(pObj)) {
    // Base case: constant-1 node (defensive; not expected to occur in this
    // assignment's test circuits, but handled to avoid undefined recursion
    // into a node with no fanin).
    result = Cudd_ReadOne(dd);  // create a BDD for constant 1
    Cudd_Ref(result);
  }
  else {
    // Recursive case: pObj is an internal AND node. Build both fanin' BDDs first, 
    // apply complement for inverted edges, then AND them together.
    DdNode* fanin0Bdd =
      Lsv_BuildCutBdd(dd, Abc_ObjFanin0(pObj), leafVarIndex, memo);
    if (Abc_ObjFaninC0(pObj)) {
      fanin0Bdd = Cudd_Not(fanin0Bdd);
    }

    DdNode* fanin1Bdd =
      Lsv_BuildCutBdd(dd, Abc_ObjFanin1(pObj), leafVarIndex, memo);
    if (Abc_ObjFaninC1(pObj)) {
      fanin1Bdd = Cudd_Not(fanin1Bdd);
    }

    result = Cudd_bddAnd(dd, fanin0Bdd, fanin1Bdd); // AND the two fanin BDDs together
    Cudd_Ref(result); // increment the reference count for the BDD node, so it won't be garbage collected by CUDD
  }

  memo[id] = result;
  return result;
}



// Compute the ROBDD size (Cudd_DagSize) of a single cut rooted at pRoot,
// with the given (sorted ascending) leaves.
//
// A brand-new DdManager is created for this cut alone, sized to exactly
// `leaves.size()` variables. The cost of rebuilding a manager per cut 
// acceptable given k <= 6 keeps cut counts and manager sizes small.
// The manager is destroyed (Cudd_Quit) immediately after reading the size.
static int Lsv_ComputeCutBddSize(Abc_Obj_t* pRoot,
  const std::vector<int>& leaves) {
  int numLeaves = static_cast<int>(leaves.size());

  // Bind each leaf's node ID to a BDD variable index: ascending leaf ID ->
  // ascending variable index -> ascending closeness to the BDD root.
  std::unordered_map<int, int> leafVarIndex;
  for (int pos = 0; pos < numLeaves; ++pos) {
    leafVarIndex[leaves[pos]] = pos;
  }

  // Pre-allocate exactly numLeaves BDD variables (index 0..numLeaves-1),
  // using standard CUDD defaults for the remaining table-sizing parameters.
  DdManager* dd =
    Cudd_Init(numLeaves, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);

  std::unordered_map<int, DdNode*> memo;
  // Main recursive BDD-building call
  DdNode* rootBdd = Lsv_BuildCutBdd(dd, pRoot, leafVarIndex, memo);

  int bddSize = Cudd_DagSize(rootBdd);

  Cudd_Quit(dd);
  return bddSize;
}


// Top-level driver for the "lsv_cut_bddsize" command: enumerate all
// k-feasible cuts of every internal AND node in the AIG (reusing the exact
// same cut-enumeration logic as lsv_cut_tt), build each cut's ROBDD, and
// print its size in the format required by the assignment.
static void Lsv_PrintCutBddSizes(Abc_Ntk_t* pNtk, int k) {
  std::vector<std::vector<Lsv_Cut_t>> allCuts;
  Lsv_EnumerateKFeasibleCuts(pNtk, k, allCuts);

  Abc_Obj_t* pNode;
  int nodeIndex;
  Abc_AigForEachAnd(pNtk, pNode, nodeIndex) {
    int id = Abc_ObjId(pNode);
    for (const Lsv_Cut_t& cut : allCuts[id]) {
      int bddSize = Lsv_ComputeCutBddSize(pNode, cut.leaves);

      printf("%d: ", id);
      for (size_t leafIdx = 0; leafIdx < cut.leaves.size(); ++leafIdx) {
        if (leafIdx > 0)
          printf(" ");
        printf("%d", cut.leaves[leafIdx]);
      }
      printf(": %d\n", bddSize);
    }
  }
}


// Parse command line for "lsv_cut_bddsize <k>"
int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Expecting an AIG (run \"strash\" first).\n");
    return 1;
  }
  if (argc != globalUtilOptind + 1) {
    goto usage;
  }

  {
    int k = atoi(argv[globalUtilOptind]);
    if (k < 1) {
      Abc_Print(-1, "Invalid k = %d: k must be >= 1.\n", k);
      return 1;
    }
    if (k > 6) {
      Abc_Print(0, "Warning: k = %d exceeds the expected range (2-6); proceeding anyway.\n", k);
    }
    Lsv_PrintCutBddSizes(pNtk, k);
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize [-h] <k>\n");
  Abc_Print(-2, "\t        enumerate k-feasible cuts and print their ROBDD sizes\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

/////////////////////////////
////////// END PA2 //////////
/////////////////////////////

/////////////////////////////
////////// END PA1 //////////
/////////////////////////////


/////////////////////////////
///////// Test Func /////////
/////////////////////////////


// 【輸出格式】
//   PI <id>                             這個 id 是 Primary Input
//   CONST1 <id>                         這個 id 是常數 1 節點（只有真的被用到才印）
//   AND <id> <f0id> <f0c> <f1id> <f1c>  內部 AND 節點：
//         f0id / f1id 是兩個 fanin 的 node id
//         f0c  / f1c  是對應 fanin 是否為反相（1=反相, 0=不反相）
//   PO <id> <fid> <fc>                  Primary Output：fid 是驅動它的 node id，
//                                        fc 是這條邊是否反相
//
// 例如講義 Fig.1 的三節點 AIG（x0=1, x1=2, x2=3；
// node5=AND(x0,~x1)；node6=AND(x1,x2)；node7=AND(node5,~node6)）
// 應該會印出：
//   PI 1
//   PI 2
//   PI 3
//   AND 5 1 0 2 1
//   AND 6 2 0 3 0
//   AND 7 5 0 6 1
//   PO ... ...
void Lsv_NtkDumpAig(Abc_Ntk_t* pNtk) {
  assert(Abc_NtkIsStrash(pNtk));  // 這個指令只在 strash 過的 AIG 上有意義

  Abc_Obj_t* pObj;
  int i;

  // ---- 印出所有 Primary Input ----
  Abc_NtkForEachPi(pNtk, pObj, i) { printf("PI %d\n", Abc_ObjId(pObj)); }

  // ---- 印出常數 1 節點（只有真的有人在用它才印，避免雜訊）----
  Abc_Obj_t* pConst1 = Abc_AigConst1(pNtk);
  if (Abc_ObjFanoutNum(pConst1) > 0) {
    printf("CONST1 %d\n", Abc_ObjId(pConst1));
  }

  // ---- 印出所有內部 AND 節點（每個節點恰好兩個 fanin）----
  Abc_NtkForEachNode(pNtk, pObj, i) {
    if (pObj == pConst1) continue;            // 常數節點已經印過了
    if (Abc_ObjFaninNum(pObj) != 2) continue;  // 防呆：只處理標準的 2-input AND

    printf("AND %d %d %d %d %d\n", Abc_ObjId(pObj), Abc_ObjId(Abc_ObjFanin0(pObj)),
      Abc_ObjFaninC0(pObj), Abc_ObjId(Abc_ObjFanin1(pObj)),
      Abc_ObjFaninC1(pObj));
  }

  // ---- 印出所有 Primary Output ----
  Abc_NtkForEachPo(pNtk, pObj, i) {
    printf("PO %d %d %d\n", Abc_ObjId(pObj), Abc_ObjId(Abc_ObjFanin0(pObj)),
      Abc_ObjFaninC0(pObj));
  }
}

int Lsv_CommandDumpAig(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (pNtk == NULL) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1,
      "This command works only on a strashed (AIG) network. "
      "Run \"strash\" first.\n");
    return 1;
  }
  Lsv_NtkDumpAig(pNtk);
  return 0;
}


////////// Example Function //////////
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