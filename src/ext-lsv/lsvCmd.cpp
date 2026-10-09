#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"
#endif

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <vector>

ABC_NAMESPACE_IMPL_START

using Lsv_Cut_t = std::vector<int>;
using Lsv_CutList_t = std::vector<Lsv_Cut_t>;
using Lsv_NodeCuts_t = std::map<int, Lsv_CutList_t>;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTruthTable(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);

static void Lsv_CutSort(Lsv_Cut_t& cut);
static Lsv_Cut_t Lsv_CutMerge(const Lsv_Cut_t& cut0, const Lsv_Cut_t& cut1, int k);
static void Lsv_CutInitPiCuts(Abc_Ntk_t* pNtk, Lsv_NodeCuts_t& nodeCuts);
static bool Lsv_CutContains(const Lsv_CutList_t& cuts, const Lsv_Cut_t& cut);
static void Lsv_CutSortList(Lsv_CutList_t& cuts);
static void Lsv_CutEnumNode(Abc_Obj_t* pNode, int k, const Lsv_NodeCuts_t& nodeCuts,
                            Lsv_CutList_t& cuts);
static void Lsv_CutEnumNtk(Abc_Ntk_t* pNtk, int k, Lsv_NodeCuts_t& nodeCuts);
static int Lsv_TruthTableSimulateRec(Abc_Obj_t* pObj, std::map<int, int>& memo,
                                     const std::map<int, int>& leafVals);
static uint64_t Lsv_TruthTableCompute(Abc_Obj_t* pRoot, const Lsv_Cut_t& cut);
static void Lsv_TruthTablePrintHex(uint64_t tt);
static void Lsv_CutPrintAll(Abc_Ntk_t* pNtk, const Lsv_NodeCuts_t& nodeCuts);
#ifdef ABC_USE_CUDD
static DdNode* Lsv_BddBuildRec(DdManager* dd, Abc_Obj_t* pObj, std::map<int, DdNode*>& memo,
                               const std::map<int, int>& leafVarIdx);
static int Lsv_BddSizeCompute(Abc_Obj_t* pRoot, const Lsv_Cut_t& cut);
#endif
static void Lsv_CutPrintBddSizeAll(Abc_Ntk_t* pNtk, const Lsv_NodeCuts_t& nodeCuts);

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

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pObj;
  int i;

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
  }
  return 0;
}

// Step 4a: merge two cuts into one (union, sort, dedupe, check size <= k).
static void Lsv_CutSort(Lsv_Cut_t& cut) {
  std::sort(cut.begin(), cut.end());
}

static Lsv_Cut_t Lsv_CutMerge(const Lsv_Cut_t& cut0, const Lsv_Cut_t& cut1, int k) {
  Lsv_Cut_t merged = cut0;
  merged.insert(merged.end(), cut1.begin(), cut1.end());
  Lsv_CutSort(merged);
  merged.erase(std::unique(merged.begin(), merged.end()), merged.end());

  if ((int)merged.size() > k) {
    return {};
  }
  return merged;
}

// Step 4b: store trivial cut {pi} for each PI.
static void Lsv_CutInitPiCuts(Abc_Ntk_t* pNtk, Lsv_NodeCuts_t& nodeCuts) {
  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachCi(pNtk, pObj, i) {
    if (Abc_ObjFanoutNum(pObj) == 0) {
      continue;
    }
    const int piId = Abc_ObjId(pObj);
    nodeCuts[piId] = Lsv_CutList_t{Lsv_Cut_t{piId}};
  }
}

static bool Lsv_CutContains(const Lsv_CutList_t& cuts, const Lsv_Cut_t& cut) {
  for (const Lsv_Cut_t& existing : cuts) {
    if (existing == cut) {
      return true;
    }
  }
  return false;
}

static void Lsv_CutSortList(Lsv_CutList_t& cuts) {
  for (Lsv_Cut_t& cut : cuts) {
    Lsv_CutSort(cut);
  }
  std::sort(cuts.begin(), cuts.end(),
            [](const Lsv_Cut_t& a, const Lsv_Cut_t& b) { return a < b; });
}

// Step 4c: enumerate cuts for one AND node.
static void Lsv_CutEnumNode(Abc_Obj_t* pNode, int k, const Lsv_NodeCuts_t& nodeCuts,
                            Lsv_CutList_t& cuts) {
  const int nodeId = Abc_ObjId(pNode);

  cuts.push_back(Lsv_Cut_t{nodeId});

  const int fanin0Id = Abc_ObjId(Abc_ObjFanin0(pNode));
  const int fanin1Id = Abc_ObjId(Abc_ObjFanin1(pNode));
  auto it0 = nodeCuts.find(fanin0Id);
  auto it1 = nodeCuts.find(fanin1Id);
  if (it0 == nodeCuts.end() || it1 == nodeCuts.end()) {
    Lsv_CutSortList(cuts);
    return;
  }

  Lsv_CutList_t mergedCuts;
  for (const Lsv_Cut_t& cut0 : it0->second) {
    for (const Lsv_Cut_t& cut1 : it1->second) {
      Lsv_Cut_t merged = Lsv_CutMerge(cut0, cut1, k);
      if (merged.empty()) {
        continue;
      }
      if (!Lsv_CutContains(mergedCuts, merged)) {
        mergedCuts.push_back(std::move(merged));
      }
    }
  }

  for (Lsv_Cut_t& cut : mergedCuts) {
    if (!Lsv_CutContains(cuts, cut)) {
      cuts.push_back(std::move(cut));
    }
  }

  Lsv_CutSortList(cuts);
}

// Step 4d: enumerate cuts for all AND nodes in topological order.
static void Lsv_CutEnumNtk(Abc_Ntk_t* pNtk, int k, Lsv_NodeCuts_t& nodeCuts) {
  Vec_Ptr_t* vNodes = Abc_AigDfs(pNtk, 0, 0);
  Abc_Obj_t* pObj;
  int i;

  Lsv_CutInitPiCuts(pNtk, nodeCuts);

  Vec_PtrForEachEntry(Abc_Obj_t*, vNodes, pObj, i) {
    if (!Abc_AigNodeIsAnd(pObj)) {
      continue;
    }
    Lsv_CutList_t cuts;
    Lsv_CutEnumNode(pObj, k, nodeCuts, cuts);
    nodeCuts[Abc_ObjId(pObj)] = std::move(cuts);
  }

  Vec_PtrFree(vNodes);
}

// Step 6: simulate AIG cone for general cuts.
static int Lsv_TruthTableSimulateRec(Abc_Obj_t* pObj, std::map<int, int>& memo,
                                     const std::map<int, int>& leafVals) {
  pObj = Abc_ObjRegular(pObj);
  const int id = Abc_ObjId(pObj);

  auto leafIt = leafVals.find(id);
  if (leafIt != leafVals.end()) {
    return leafIt->second;
  }

  auto memoIt = memo.find(id);
  if (memoIt != memo.end()) {
    return memoIt->second;
  }

  if (Abc_AigNodeIsConst(pObj)) {
    memo[id] = 1;
    return 1;
  }

  if (Abc_AigNodeIsAnd(pObj)) {
    int v0 = Lsv_TruthTableSimulateRec(Abc_ObjFanin0(pObj), memo, leafVals);
    int v1 = Lsv_TruthTableSimulateRec(Abc_ObjFanin1(pObj), memo, leafVals);
    if (Abc_ObjFaninC0(pObj)) {
      v0 = !v0;
    }
    if (Abc_ObjFaninC1(pObj)) {
      v1 = !v1;
    }
    memo[id] = v0 & v1;
    return memo[id];
  }

  memo[id] = 0;
  return 0;
}

static uint64_t Lsv_TruthTableCompute(Abc_Obj_t* pRoot, const Lsv_Cut_t& cut) {
  const int k = (int)cut.size();

  if (k == 1 && cut[0] == (int)Abc_ObjId(pRoot)) {
    return 0x2;
  }

  uint64_t tt = 0;
  for (int i = 0; i < (1 << k); ++i) {
    std::map<int, int> leafVals;
    for (int j = 0; j < k; ++j) {
      leafVals[cut[j]] = (i >> (k - 1 - j)) & 1;
    }

    std::map<int, int> memo;
    if (Lsv_TruthTableSimulateRec(pRoot, memo, leafVals)) {
      tt |= (1ULL << i);
    }
  }
  return tt;
}

static void Lsv_TruthTablePrintHex(uint64_t tt) {
  char buffer[32];
  std::snprintf(buffer, sizeof(buffer), "%llx", (unsigned long long)tt);

  char* p = buffer;
  while (p[0] == '0' && p[1] != '\0') {
    ++p;
  }
  std::printf("%s", p);
}

static void Lsv_CutPrintAll(Abc_Ntk_t* pNtk, const Lsv_NodeCuts_t& nodeCuts) {
  Abc_Obj_t* pObj;
  int i;

  Abc_AigForEachAnd(pNtk, pObj, i) {
    const int nodeId = Abc_ObjId(pObj);
    auto it = nodeCuts.find(nodeId);
    if (it == nodeCuts.end()) {
      continue;
    }

    for (const Lsv_Cut_t& cut : it->second) {
      const uint64_t tt = Lsv_TruthTableCompute(pObj, cut);

      printf("%d:", nodeId);
      for (int leaf : cut) {
        printf(" %d", leaf);
      }
      printf(": ");
      Lsv_TruthTablePrintHex(tt);
      printf("\n");
    }
  }
}

#ifdef ABC_USE_CUDD
// Step 4.2-3: build cut BDD by cone traversal (parallel to truth-table simulation).
static DdNode* Lsv_BddBuildRec(DdManager* dd, Abc_Obj_t* pObj, std::map<int, DdNode*>& memo,
                               const std::map<int, int>& leafVarIdx) {
  pObj = Abc_ObjRegular(pObj);
  const int id = Abc_ObjId(pObj);

  auto leafIt = leafVarIdx.find(id);
  if (leafIt != leafVarIdx.end()) {
    return Cudd_bddIthVar(dd, leafIt->second);
  }

  auto memoIt = memo.find(id);
  if (memoIt != memo.end()) {
    return memoIt->second;
  }

  if (Abc_AigNodeIsConst(pObj)) {
    DdNode* bFunc = dd->one;
    Cudd_Ref(bFunc);
    memo[id] = bFunc;
    return bFunc;
  }

  if (Abc_AigNodeIsAnd(pObj)) {
    DdNode* bFunc0 = Lsv_BddBuildRec(dd, Abc_ObjFanin0(pObj), memo, leafVarIdx);
    DdNode* bFunc1 = Lsv_BddBuildRec(dd, Abc_ObjFanin1(pObj), memo, leafVarIdx);
    Cudd_Ref(bFunc0);
    Cudd_Ref(bFunc1);
    bFunc0 = Cudd_NotCond(bFunc0, Abc_ObjFaninC0(pObj));
    bFunc1 = Cudd_NotCond(bFunc1, Abc_ObjFaninC1(pObj));
    DdNode* bFunc = Cudd_bddAnd(dd, bFunc0, bFunc1);
    Cudd_Ref(bFunc);
    Cudd_RecursiveDeref(dd, bFunc0);
    Cudd_RecursiveDeref(dd, bFunc1);
    memo[id] = bFunc;
    return bFunc;
  }

  DdNode* bFunc = Cudd_ReadLogicZero(dd);
  Cudd_Ref(bFunc);
  memo[id] = bFunc;
  return bFunc;
}

static int Lsv_BddSizeCompute(Abc_Obj_t* pRoot, const Lsv_Cut_t& cut) {
  const int k = (int)cut.size();
  DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);

  std::map<int, int> leafVarIdx;
  for (int j = 0; j < k; ++j) {
    leafVarIdx[cut[j]] = j;
  }

  std::map<int, DdNode*> memo;
  DdNode* bFunc = Lsv_BddBuildRec(dd, pRoot, memo, leafVarIdx);
  const int size = Cudd_DagSize(bFunc);

  for (const auto& entry : memo) {
    Cudd_RecursiveDeref(dd, entry.second);
  }
  Cudd_Quit(dd);
  return size;
}
#endif

static void Lsv_CutPrintBddSizeAll(Abc_Ntk_t* pNtk, const Lsv_NodeCuts_t& nodeCuts) {
  Abc_Obj_t* pObj;
  int i;

  Abc_AigForEachAnd(pNtk, pObj, i) {
    const int nodeId = Abc_ObjId(pObj);
    auto it = nodeCuts.find(nodeId);
    if (it == nodeCuts.end()) {
      continue;
    }

    for (const Lsv_Cut_t& cut : it->second) {
      printf("%d:", nodeId);
      for (int leaf : cut) {
        printf(" %d", leaf);
      }
      printf(": ");
#ifdef ABC_USE_CUDD
      printf("%d", Lsv_BddSizeCompute(pObj, cut));
#else
      printf("0");
#endif
      printf("\n");
    }
  }
}

static int Lsv_CommandCutTruthTable(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Lsv_NodeCuts_t nodeCuts;
  int k;

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "This command works only for AIGs (run \"strash\").\n");
    return 1;
  }
  if (argc < 2) {
    Abc_Print(-1, "Missing cut size parameter <k>.\n");
    Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
    return 1;
  }

  k = atoi(argv[1]);
  if (k < 2 || k > 6) {
    Abc_Print(-1, "Invalid cut size k = %d (expected 2 <= k <= 6).\n", k);
    return 1;
  }

  Lsv_CutEnumNtk(pNtk, k, nodeCuts);
  Lsv_CutPrintAll(pNtk, nodeCuts);
  return 0;
}

static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int k;

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "This command works only for AIGs (run \"strash\").\n");
    return 1;
  }
  if (argc < 2) {
    Abc_Print(-1, "Missing cut size parameter <k>.\n");
    Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
    return 1;
  }

  k = atoi(argv[1]);
  if (k < 2 || k > 6) {
    Abc_Print(-1, "Invalid cut size k = %d (expected 2 <= k <= 6).\n", k);
    return 1;
  }

  Lsv_NodeCuts_t nodeCuts;
  Lsv_CutEnumNtk(pNtk, k, nodeCuts);
  Lsv_CutPrintBddSizeAll(pNtk, nodeCuts);
  return 0;
}

ABC_NAMESPACE_IMPL_END
