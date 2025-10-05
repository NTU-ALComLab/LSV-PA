#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_mocut", Lsv_CommandPrintMoCut, 0);
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

// ==================== lsv_printmocut：k-l multi-output cut (Method 1) ====================
#include <vector>
#include <unordered_map>
#include <algorithm>

// 前置宣告（供 init() 註冊用）

namespace { // 只在本檔可見的工具

//（工程可調）每節點最多保留的 cut 數量；設 0 代表不設上限
#ifndef LSV_PER_NODE_CUT_LIMIT
#define LSV_PER_NODE_CUT_LIMIT 0
#endif

// A,B 為升冪且無重複；輸出 C = A∪B；過程若 |C|>k 直接回 false（早停）
static inline bool UnionSortedUpToK(const std::vector<int>& A,
                                    const std::vector<int>& B,
                                    int k,
                                    std::vector<int>& C) {
  C.clear();
  C.reserve(std::min(k, (int)A.size() + (int)B.size()));
  size_t i = 0, j = 0;
  while (i < A.size() || j < B.size()) {
    int v;
    if (j >= B.size() || (i < A.size() && A[i] < B[j])) v = A[i++];
    else if (i >= A.size() || B[j] < A[i])              v = B[j++];
    else { v = A[i]; ++i; ++j; } // equal
    if (C.empty() || C.back() != v) C.push_back(v);
    if ((int)C.size() > k) return false;
  }
  return true;
}

// 檢查 M ⊆ C（兩者皆為升冪、無重複）
static inline bool IsSubset(const std::vector<int>& M, const std::vector<int>& C) {
  size_t i = 0, j = 0;
  while (i < M.size() && j < C.size()) {
    if (M[i] == C[j]) { ++i; ++j; }
    else if (M[i] > C[j]) { ++j; }
    else { return false; } // M[i] < C[j]
  }
  return i == M.size();
}

// 移除重複並按大小排序；可選每節點上限
static std::vector<std::vector<int>>
MinimalAntichain(std::vector<std::vector<int>>& cand, int perNodeLimit /*0=unlimited*/) {
  std::sort(cand.begin(), cand.end(), [](const auto& a, const auto& b){
    if (a.size() != b.size()) return a.size() < b.size();
    return a < b;
  });
  cand.erase(std::unique(cand.begin(), cand.end()), cand.end());

  // 暫時先返回所有候選 cut，看看是否會生成 3-node cut
  std::vector<std::vector<int>> keep;
  keep.reserve(cand.size());
  
  for (const auto& C : cand) {
    keep.push_back(C);
    if (perNodeLimit > 0 && (int)keep.size() >= perNodeLimit) break; // 上限（若有）
  }
  return keep;
}

// 主要流程：列舉每個節點的 k-feasible cuts（leaf=PI），聚合同一組 leaf 的「輸出節點」數（只計 AND）
static int PrintMoCut(Abc_Ntk_t* pNtk, int k, int l) {
  if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1; }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Please 'strash' the network first (AIG required).\n");
    return 1;
  }
  if (k <= 0 || l <= 0) {
    Abc_Print(-1, "k and l must be positive integers.\n");
    return 1;
  }

  // cuts[id] = 該節點的所有 cut；每個 cut 是升冪 PI ID 的向量
  int maxId = Abc_NtkObjNumMax(pNtk);
  std::vector<std::vector<std::vector<int>>> cuts(maxId + 1);

  // 使用助教建議的方法：Abc_NtkForEachObj() 在 strash 後會按拓撲順序遍歷
  Abc_Obj_t* pObj = nullptr; int i = 0;

  // 初始化：每個 PI 的唯一 cut = {pi_id}
  Abc_NtkForEachPi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    cuts[id].push_back(std::vector<int>{id});
  }

  // 全域聚合：leaf-set → 共享此 cut 的 AND 節點 IDs
  struct VecHash {
    size_t operator()(const std::vector<int>& v) const {
      size_t h = 1469598103934665603ull; // FNV-ish seed
      for (int x : v) { h ^= (size_t)x + 0x9e3779b97f4a7c15ull + (h<<6) + (h>>2); }
      return h;
    }
  };
  struct VecEq {
    bool operator()(const std::vector<int>& a, const std::vector<int>& b) const { return a == b; }
  };
  std::unordered_map<std::vector<int>, std::vector<int>, VecHash, VecEq> gmap;

  // 依等級序處理 AND 節點：pairwise 合併左右子 cuts → antichain → 記入 gmap
  Abc_NtkForEachObj(pNtk, pObj, i) {
    if (!pObj) continue;
    if (!Abc_AigNodeIsAnd(pObj)) continue;

    int vId = Abc_ObjId(pObj);
    int aId = Abc_ObjFaninId0(pObj);
    int bId = Abc_ObjFaninId1(pObj);

    std::vector<std::vector<int>> cand;
    cand.reserve(std::max<size_t>(8, cuts[aId].size() * std::max<size_t>(1, cuts[bId].size())));
    std::vector<int> tmp;

    // 1. 合并两个fanin的cuts (现有的逻辑)
    for (const auto& A : cuts[aId]) {
      for (const auto& B : cuts[bId]) {
        if (UnionSortedUpToK(A, B, k, tmp)) {
          cand.push_back(tmp);
        }
      }
    }

    // 2. 添加混合cuts: 使用左fanin节点 + 右fanin的PI cuts
    for (const auto& B : cuts[bId]) {
      std::vector<int> mixed_cut = {aId};  // 包含左fanin节点
      if (UnionSortedUpToK(mixed_cut, B, k, tmp)) {
        cand.push_back(tmp);
      }
    }

    // 3. 添加混合cuts: 使用左fanin的PI cuts + 右fanin节点
    for (const auto& A : cuts[aId]) {
      std::vector<int> mixed_cut = {bId};  // 包含右fanin节点
      if (UnionSortedUpToK(A, mixed_cut, k, tmp)) {
        cand.push_back(tmp);
      }
    }

    // 4. 添加间接cuts: 使用两个fanin节点
    std::vector<int> indirect_cut = {aId, bId};
    if (indirect_cut.size() <= (size_t)k) {
      cand.push_back(indirect_cut);
    }

    auto keep = MinimalAntichain(cand, LSV_PER_NODE_CUT_LIMIT);
    cuts[vId] = std::move(keep);


    for (const auto& C : cuts[vId]) {
      gmap[C].push_back(vId); // 只把 AND 節點當「輸出」統計
    }
  }

  // 列印：共享此 cut 的 AND 節點數量 ≥ l，按cut的第一个数字排序
  std::vector<std::pair<std::vector<int>, std::vector<int>>> sorted_results;
  
  for (auto& kv : gmap) {
    auto& outs = kv.second;
    std::sort(outs.begin(), outs.end());
    outs.erase(std::unique(outs.begin(), outs.end()), outs.end());
    if ((int)outs.size() >= l) {
      sorted_results.push_back({kv.first, outs});
    }
  }
  
  // 按cut的第一个数字排序
  std::sort(sorted_results.begin(), sorted_results.end(), 
    [](const auto& a, const auto& b) {
      return a.first[0] < b.first[0];
    });
  
  // 输出排序后的结果
  for (const auto& result : sorted_results) {
    const auto& cut = result.first;
    const auto& outs = result.second;
    
    // 左：cut（PI IDs）
    for (size_t t = 0; t < cut.size(); ++t) {
      if (t) printf(" ");
      printf("%d", cut[t]);
    }
    printf(" : ");
    // 右：覆蓋的 AND 節點 IDs
    for (size_t t = 0; t < outs.size(); ++t) {
      if (t) printf(" ");
      printf("%d", outs[t]);
    }
    printf("\n");
  }
  
  // 输出总行数
  //printf("Total: %zu k-l multi-output cuts\n", sorted_results.size());

  return 0;
}

} // end anonymous namespace

// 指令進入點： lsv_printmocut <k> <l>
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  int c, k = -1, l = -1;
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h': goto usage;
      default : goto usage;
    }
  }
  if (argc - globalUtilOptind != 2) goto usage;
  k = atoi(argv[globalUtilOptind + 0]);
  l = atoi(argv[globalUtilOptind + 1]);

  if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1; }

  return PrintMoCut(pNtk, k, l);

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
  Abc_Print(-2, "    Enumerate k-l multi-output cuts.\n");
  Abc_Print(-2, "    - Leaves: PI IDs\n");
  Abc_Print(-2, "    - Outputs counted: AND node IDs (ignore POs & PIs)\n");
  Abc_Print(-2, "    k : max cut size (positive integer)\n");
  Abc_Print(-2, "    l : min number of AND outputs sharing the same leaf-set (positive integer)\n");
  Abc_Print(-2, "    -h: show this help\n");
  return 1;
}
// ==================== end of lsv_printmocut ====================
