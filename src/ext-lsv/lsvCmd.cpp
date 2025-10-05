#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <string>


static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMocut, 0);
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

// -------------------- Multi-output k-feasible cut enumeration --------------------

namespace {

// Performance cap to prevent explosion on large designs
static const size_t LSV_MAX_CUTS_PER_NODE = 512;

// Memoization of reachability queries: fromId -> targetId
static std::unordered_map<unsigned long long, char> gReachMemo;

// Helper: DFS to check if target is in transitive fanin of from.
static bool Lsv_IsInTransitiveFanin(Abc_Obj_t* from, Abc_Obj_t* target) {
  if (from == target) return true;
  if (Abc_ObjIsCi(from)) return false;
  std::vector<Abc_Obj_t*> stack;
  stack.push_back(from);
  std::unordered_set<int> visited;
  while (!stack.empty()) {
    Abc_Obj_t* cur = stack.back();
    stack.pop_back();
    int id = Abc_ObjId(cur);
    if (visited.find(id) != visited.end()) continue;
    visited.insert(id);
    if (cur == target) return true;
    if (Abc_ObjIsCi(cur)) continue;
    Abc_Obj_t* pFanin; int k;
    Abc_ObjForEachFanin(cur, pFanin, k) stack.push_back(pFanin);
  }
  return false;
}

// Reduce redundant leaves: remove any leaf that is in transitive fanin of another leaf
static void Lsv_ReduceIrredundant(std::vector<int>& leaves, Abc_Ntk_t* pNtk) {
  if (leaves.size() <= 1) return;
  std::sort(leaves.begin(), leaves.end());
  leaves.erase(std::unique(leaves.begin(), leaves.end()), leaves.end());
  std::vector<int> keep;
  keep.reserve(leaves.size());
  for (size_t i = 0; i < leaves.size(); ++i) {
    bool dominated = false;
    Abc_Obj_t* leaf_i = Abc_NtkObj(pNtk, leaves[i]);
    for (size_t j = 0; j < leaves.size() && !dominated; ++j) {
      if (i == j) continue;
      Abc_Obj_t* leaf_j = Abc_NtkObj(pNtk, leaves[j]);
      unsigned long long key = (((unsigned long long)Abc_ObjId(leaf_j)) << 32) | (unsigned long long)Abc_ObjId(leaf_i);
      auto it = gReachMemo.find(key);
      bool reach = false;
      if (it != gReachMemo.end()) reach = (it->second != 0);
      else {
        reach = Lsv_IsInTransitiveFanin(leaf_j, leaf_i);
        gReachMemo.emplace(key, reach ? 1 : 0);
      }
      if (reach) dominated = true;
    }
    if (!dominated) keep.push_back(leaves[i]);
  }
  leaves.swap(keep);
}

static std::string Lsv_LeavesKey(const std::vector<int>& leaves) {
  std::string s;
  s.reserve(leaves.size() * 6);
  for (size_t i = 0; i < leaves.size(); ++i) {
    if (i) s.push_back(' ');
    s += std::to_string(leaves[i]);
  }
  return s;
}

}  // namespace

static int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1; }
  if (!Abc_NtkIsStrash(pNtk)) { Abc_Print(-1, "The current network is not an AIG (strashed). Run 'strash' first.\n"); return 1; }

  int c; int k = 0, l = 0;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
        Abc_Print(-2, "\t        enumerate k-l multi-output cuts (3<=k<=6, 1<=l<=4)\n");
        Abc_Print(-2, "\t-h    : print the command usage\n");
        return 1;
      default:
        Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
        Abc_Print(-2, "\t        enumerate k-l multi-output cuts (3<=k<=6, 1<=l<=4)\n");
        Abc_Print(-2, "\t-h    : print the command usage\n");
        return 1;
    }
  }
  if (argc < 3) {
    Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
    Abc_Print(-2, "\t        enumerate k-l multi-output cuts (3<=k<=6, 1<=l<=4)\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
  }
  k = atoi(argv[1]); l = atoi(argv[2]);
  if (k < 3 || k > 6 || l < 1 || l > 4) { Abc_Print(-1, "Parameter out of range. Require 3 <= k <= 6 and 1 <= l <= 4.\n"); return 1; }

  int nObjs = Abc_NtkObjNumMax(pNtk);
  std::vector<std::vector<std::vector<int>>> nodeCuts; nodeCuts.resize(nObjs);

  Abc_Obj_t* pObj; int i;
  Abc_NtkForEachCi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    nodeCuts[id].push_back(std::vector<int>{id});
  }

  Vec_Ptr_t* vDfs = Abc_NtkDfs(pNtk, 0);
  int nDfs = Vec_PtrSize(vDfs);
  for (int idx = 0; idx < nDfs; ++idx) {
    Abc_Obj_t* pNode = (Abc_Obj_t*)Vec_PtrEntry(vDfs, idx);
    if (!Abc_ObjIsNode(pNode)) continue;
    Abc_Obj_t* pF0 = Abc_ObjFanin(pNode, 0);
    Abc_Obj_t* pF1 = Abc_ObjFanin(pNode, 1);
    int idNode = Abc_ObjId(pNode);
    int id0 = Abc_ObjId(pF0);
    int id1 = Abc_ObjId(pF1);

    if (Abc_ObjIsCi(pF0) && nodeCuts[id0].empty()) nodeCuts[id0].push_back(std::vector<int>{id0});
    if (Abc_ObjIsCi(pF1) && nodeCuts[id1].empty()) nodeCuts[id1].push_back(std::vector<int>{id1});

    std::unordered_set<std::string> seen;
    {
      std::vector<int> unit{ idNode };
      std::sort(unit.begin(), unit.end());
      std::string key = Lsv_LeavesKey(unit);
      if (seen.insert(key).second) nodeCuts[idNode].push_back(std::move(unit));
    }
    for (const auto& ca : nodeCuts[id0]) {
      for (const auto& cb : nodeCuts[id1]) {
        if (nodeCuts[idNode].size() >= LSV_MAX_CUTS_PER_NODE) break;
        std::vector<int> merged;
        merged.reserve(ca.size() + cb.size());
        merged.insert(merged.end(), ca.begin(), ca.end());
        merged.insert(merged.end(), cb.begin(), cb.end());
        std::sort(merged.begin(), merged.end());
        merged.erase(std::unique(merged.begin(), merged.end()), merged.end());
        if ((int)merged.size() > k) continue;
        if ((int)merged.size() > k || merged.empty()) continue;
        std::string key = Lsv_LeavesKey(merged);
        if (seen.insert(key).second) {
          nodeCuts[idNode].push_back(std::move(merged));
          if (nodeCuts[idNode].size() >= LSV_MAX_CUTS_PER_NODE) break;
        }
      }
      if (nodeCuts[idNode].size() >= LSV_MAX_CUTS_PER_NODE) break;
    }
  }

  std::unordered_map<std::string, std::vector<int>> cutToOutputs;

  // Per-node DP pruning: remove dominated cuts (subset dominance)
  for (int idx = 0; idx < nDfs; ++idx) {
    Abc_Obj_t* pNode = (Abc_Obj_t*)Vec_PtrEntry(vDfs, idx);
    if (!Abc_ObjIsNode(pNode)) continue;
    auto& cuts = nodeCuts[Abc_ObjId(pNode)];
    if (cuts.size() <= 1) continue;
    // sort by size then lex
    std::sort(cuts.begin(), cuts.end(), [](const std::vector<int>& a, const std::vector<int>& b){
      if (a.size() != b.size()) return a.size() < b.size();
      return a < b;
    });
    std::vector<char> removed(cuts.size(), 0);
    for (size_t i = 0; i < cuts.size(); ++i) {
      if (removed[i]) continue;
      for (size_t j = i + 1; j < cuts.size(); ++j) {
        if (removed[j]) continue;
        // since cuts[i] is not larger than cuts[j], check subset
        size_t pi = 0, pj = 0;
        const auto& A = cuts[i];
        const auto& B = cuts[j];
        while (pi < A.size() && pj < B.size()) {
          if (A[pi] == B[pj]) { ++pi; ++pj; }
          else if (A[pi] > B[pj]) { ++pj; }
          else break;
        }
        if (pi == A.size()) removed[j] = 1;
      }
    }
    std::vector<std::vector<int>> kept;
    kept.reserve(cuts.size());
    for (size_t t = 0; t < cuts.size(); ++t) if (!removed[t]) kept.push_back(std::move(cuts[t]));
    cuts.swap(kept);
  }

  Abc_NtkForEachCi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const auto& cut : nodeCuts[id]) {
      std::vector<int> leaves = cut;
      std::sort(leaves.begin(), leaves.end());
      std::string key = Lsv_LeavesKey(leaves);
      auto& outs = cutToOutputs[key];
      outs.push_back(id);
    }
  }

  for (int idx = 0; idx < nDfs; ++idx) {
    Abc_Obj_t* pNode = (Abc_Obj_t*)Vec_PtrEntry(vDfs, idx);
    if (!Abc_ObjIsNode(pNode)) continue;
    int idNode = Abc_ObjId(pNode);
    for (const auto& cut : nodeCuts[idNode]) {
      std::vector<int> leaves = cut;
      std::sort(leaves.begin(), leaves.end());
      std::string key = Lsv_LeavesKey(leaves);
      auto& outs = cutToOutputs[key];
      outs.push_back(idNode);
    }
  }

  for (auto& kv : cutToOutputs) {
    auto& outs = kv.second;
    std::sort(outs.begin(), outs.end());
    outs.erase(std::unique(outs.begin(), outs.end()), outs.end());
    if ((int)outs.size() < l) continue;
    const std::string& key = kv.first;
    printf("%s :", key.c_str());
    for (size_t t = 0; t < outs.size(); ++t) printf(" %d", outs[t]);
    printf("\n");
  }

  Vec_PtrFree(vDfs);
  return 0;
}