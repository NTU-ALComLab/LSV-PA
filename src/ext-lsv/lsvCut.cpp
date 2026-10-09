#include "ext-lsv/lsvCut.h"

extern "C" {
#include "bdd/cudd/cudd.h"
}

#include <algorithm>
#include <cstdint>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

static std::vector<int> Lsv_UnionLeaves(const std::vector<int>& a,
                                        const std::vector<int>& b) {
  std::vector<int> out;
  out.reserve(a.size() + b.size());
  size_t i = 0;
  size_t j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] == b[j]) {
      out.push_back(a[i]);
      i++;
      j++;
    } else if (a[i] < b[j]) {
      out.push_back(a[i]);
      i++;
    } else {
      out.push_back(b[j]);
      j++;
    }
  }
  while (i < a.size()) {
    out.push_back(a[i]);
    i++;
  }
  while (j < b.size()) {
    out.push_back(b[j]);
    j++;
  }
  return out;
}

// Leaf sets only. A cut's function is evaluated later with these leaves free,
// so a leaf is not expanded into its own fanins.
static void Lsv_EnumerateLeaves(
    Abc_Ntk_t* pNtk, int k,
    std::vector<std::vector<std::vector<int>>>& cuts) {
  cuts.assign(Abc_NtkObjNumMax(pNtk), {});

  Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
  cuts[Abc_ObjId(pConst)].push_back({});

  Abc_Obj_t* pCi;
  int i;
  Abc_NtkForEachCi(pNtk, pCi, i) {
    cuts[Abc_ObjId(pCi)].push_back({(int)Abc_ObjId(pCi)});
  }

  Abc_Obj_t* pNode;
  Abc_AigForEachAnd(pNtk, pNode, i) {
    std::vector<std::vector<int>>& nodeCuts = cuts[Abc_ObjId(pNode)];
    std::set<std::vector<int>> seen;
    nodeCuts.push_back({(int)Abc_ObjId(pNode)});
    seen.insert(nodeCuts.back());

    const std::vector<std::vector<int>>& cuts0 =
        cuts[Abc_ObjId(Abc_ObjFanin0(pNode))];
    const std::vector<std::vector<int>>& cuts1 =
        cuts[Abc_ObjId(Abc_ObjFanin1(pNode))];
    for (const std::vector<int>& c0 : cuts0) {
      for (const std::vector<int>& c1 : cuts1) {
        std::vector<int> leaves = Lsv_UnionLeaves(c0, c1);
        if ((int)leaves.size() > k || !seen.insert(leaves).second) {
          continue;
        }
        nodeCuts.push_back(leaves);
      }
    }
  }
}

static int Lsv_EvalNode(Abc_Obj_t* pNode, const std::unordered_map<int, int>& leaves,
                        std::unordered_map<int, int>& memo) {
  const int id = Abc_ObjId(pNode);
  const auto leaf = leaves.find(id);
  if (leaf != leaves.end()) {
    return leaf->second;
  }
  const auto cached = memo.find(id);
  if (cached != memo.end()) {
    return cached->second;
  }
  if (Abc_AigNodeIsConst(pNode)) {
    memo[id] = 1;
    return 1;
  }
  const int v0 = Lsv_EvalNode(Abc_ObjFanin0(pNode), leaves, memo) ^
                 Abc_ObjFaninC0(pNode);
  const int v1 = Lsv_EvalNode(Abc_ObjFanin1(pNode), leaves, memo) ^
                 Abc_ObjFaninC1(pNode);
  const int value = v0 & v1;
  memo[id] = value;
  return value;
}

// Smallest leaf id is the MSB of the assignment index.
static uint64_t Lsv_Truth(Abc_Obj_t* pNode, const std::vector<int>& leaves) {
  const int n = (int)leaves.size();
  uint64_t tt = 0;
  const uint64_t limit = 1ull << n;
  for (uint64_t i = 0; i < limit; i++) {
    std::unordered_map<int, int> assign;
    assign.reserve(leaves.size());
    for (int j = 0; j < n; j++) {
      assign[leaves[j]] = (int)((i >> (n - 1 - j)) & 1ull);
    }
    std::unordered_map<int, int> memo;
    if (Lsv_EvalNode(pNode, assign, memo)) {
      tt |= 1ull << i;
    }
  }
  return tt;
}

static DdNode* Lsv_NotCond(DdNode* node, int complement) {
  return (DdNode*)((uintptr_t)node ^ (uintptr_t)complement);
}

static DdNode* Lsv_EvalBdd(DdManager* mgr, Abc_Obj_t* pNode,
                           const std::unordered_set<int>& leaves,
                           std::unordered_map<int, DdNode*>& memo) {
  const int id = Abc_ObjId(pNode);
  if (leaves.count(id)) {
    return Cudd_bddIthVar(mgr, id);
  }
  const auto cached = memo.find(id);
  if (cached != memo.end()) {
    return cached->second;
  }
  if (Abc_AigNodeIsConst(pNode)) {
    return Cudd_ReadOne(mgr);
  }
  DdNode* f0 = Lsv_NotCond(
      Lsv_EvalBdd(mgr, Abc_ObjFanin0(pNode), leaves, memo),
      Abc_ObjFaninC0(pNode));
  DdNode* f1 = Lsv_NotCond(
      Lsv_EvalBdd(mgr, Abc_ObjFanin1(pNode), leaves, memo),
      Abc_ObjFaninC1(pNode));
  DdNode* f = Cudd_bddAnd(mgr, f0, f1);
  if (f == nullptr) {
    return nullptr;
  }
  Cudd_Ref(f);
  memo[id] = f;
  return f;
}

static void Lsv_DerefMemo(DdManager* mgr,
                          std::unordered_map<int, DdNode*>& memo) {
  for (const auto& entry : memo) {
    Cudd_RecursiveDeref(mgr, entry.second);
  }
  memo.clear();
}

static void Lsv_PrintLeaves(int id, const std::vector<int>& leaves) {
  printf("%d:", id);
  for (int leaf : leaves) {
    printf(" %d", leaf);
  }
}

void Lsv_PrintCutTruth(Abc_Ntk_t* pNtk, int k) {
  std::vector<std::vector<std::vector<int>>> cuts;
  Lsv_EnumerateLeaves(pNtk, k, cuts);

  Abc_Obj_t* pNode;
  int i;
  Abc_AigForEachAnd(pNtk, pNode, i) {
    const int id = Abc_ObjId(pNode);
    for (const std::vector<int>& leaves : cuts[id]) {
      Lsv_PrintLeaves(id, leaves);
      printf(": %llX\n", (unsigned long long)Lsv_Truth(pNode, leaves));
    }
  }
}

void Lsv_PrintCutBddSize(Abc_Ntk_t* pNtk, int k) {
  DdManager* mgr = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  if (mgr == nullptr) {
    Abc_Print(-1, "CUDD initialization failed.\n");
    return;
  }

  std::vector<std::vector<std::vector<int>>> cuts;
  Lsv_EnumerateLeaves(pNtk, k, cuts);

  Abc_Obj_t* pNode;
  int i;
  Abc_AigForEachAnd(pNtk, pNode, i) {
    const int id = Abc_ObjId(pNode);
    for (const std::vector<int>& leaves : cuts[id]) {
      std::unordered_set<int> leafSet(leaves.begin(), leaves.end());
      std::unordered_map<int, DdNode*> memo;
      DdNode* f = Lsv_EvalBdd(mgr, pNode, leafSet, memo);
      if (f == nullptr) {
        Lsv_DerefMemo(mgr, memo);
        Cudd_Quit(mgr);
        Abc_Print(-1, "CUDD ran out of memory.\n");
        return;
      }
      Lsv_PrintLeaves(id, leaves);
      printf(": %d\n", Cudd_DagSize(f));
      Lsv_DerefMemo(mgr, memo);
    }
  }
  Cudd_Quit(mgr);
}
