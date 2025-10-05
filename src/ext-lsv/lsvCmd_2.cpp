// src/ext-lsv/lsv_mocut.cpp
extern "C" {
  #include "base/abc/abc.h"
  #include "base/main/main.h"
  #include "base/main/mainInt.h"
}

#include <algorithm>
#include <cstdint>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

// ---------- 小工具：統一把 ABC 物件 ID 轉成 int（避免 list-init 縮窄錯誤） ----------
inline int ID(Abc_Obj_t* o) { return static_cast<int>(Abc_ObjId(o)); }

// ---------- 工具：小型 hash key for vector<int> ----------
struct VecHash {
  size_t operator()(const std::vector<int>& v) const noexcept {
    size_t h = 1469598103934665603ull;
    for (int x : v) { h ^= (size_t)x; h *= 1099511628211ull; }
    return h;
  }
};
struct VecEq {
  bool operator()(const std::vector<int>& a, const std::vector<int>& b) const noexcept {
    return a == b;
  }
};

// ---------- 到達性查詢（是否 u 是 v 的祖先）含快取 ----------
static std::unordered_map<uint64_t, bool> sReachMemo;

static bool IsAncestor(Abc_Obj_t* u, Abc_Obj_t* v) {
  int uid = ID(u), vid = ID(v);
  if (uid == vid) return true;
  uint64_t key = ((uint64_t)uid << 32) | (uint32_t)vid;
  auto it = sReachMemo.find(key);
  if (it != sReachMemo.end()) return it->second;

  // DFS from v backward to PIs; if we meet u -> true
  std::vector<int> stk;
  std::unordered_set<int> vis;
  stk.push_back(vid);
  while (!stk.empty()) {
    int id = stk.back(); stk.pop_back();
    if (id == uid) { sReachMemo[key] = true; return true; }
    if (!vis.insert(id).second) continue;
    Abc_Obj_t* x = Abc_NtkObj(v->pNtk, id);
    if (Abc_ObjIsPi(x)) continue;
    Abc_Obj_t* fi; int i;
    Abc_ObjForEachFanin(x, fi, i) stk.push_back(ID(fi));
  }
  sReachMemo[key] = false;
  return false;
}

// ---------- 讓葉集合 irredundant：若 a 是 b 的祖先，移除 a ----------
static void MakeIrredundant(std::vector<int>& leaves, Abc_Ntk_t* pNtk) {
  // leaves 已排序
  std::vector<int> keep;
  for (size_t i = 0; i < leaves.size(); ++i) {
    int id_i = leaves[i];
    bool dominated = false;
    for (size_t j = 0; j < leaves.size(); ++j) {
      if (i == j) continue;
      int id_j = leaves[j];
      Abc_Obj_t* oi = Abc_NtkObj(pNtk, id_i);
      Abc_Obj_t* oj = Abc_NtkObj(pNtk, id_j);
      // 如果 oi 是 oj 的祖先 -> 刪掉 oi（保留靠近根的葉）
      if (IsAncestor(oi, oj)) { dominated = true; break; }
    }
    if (!dominated) keep.push_back(id_i);
  }
  leaves.swap(keep);
  std::sort(leaves.begin(), leaves.end());
  leaves.erase(std::unique(leaves.begin(), leaves.end()), leaves.end());
}

// ---------- 指令主體 ----------
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  // 參數
  if (argc != 3) {
    Abc_Print(-1, "usage: lsv_printmocut <k> <l>\n");
    return 1;
  }
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);
  if (k < 3 || k > 6 || l < 2 || l > 4) { // 公告：l 介於 2~4
    Abc_Print(-1, "error: k in [3..6], l in [2..4]\n");
    return 1;
  }

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1; }

  // 轉成 AIG
  if (!Abc_NtkIsStrash(pNtk)) {
    if (Cmd_CommandExecute(pAbc, "strash")) {
      Abc_Print(-1, "error: failed to strash\n"); return 1;
    }
    pNtk = Abc_FrameReadNtk(pAbc);
    if (!Abc_NtkIsStrash(pNtk)) {
      Abc_Print(-1, "error: network is not AIG\n"); return 1;
    }
  }

  // 取得 PIs 與 AND nodes（作為 roots）
  std::vector<Abc_Obj_t*> pis, ands;
  Abc_Obj_t* pObj; int i;
  Abc_NtkForEachPi(pNtk, pObj, i) pis.push_back(pObj);
  Abc_NtkForEachNode(pNtk, pObj, i) ands.push_back(pObj); // strash 下即 ANDs

  // 每個節點的 cut 集合（vector<int> 代表葉的 ID；已排序）
  std::vector<std::unordered_set<std::vector<int>, VecHash, VecEq>>
      nodeCuts(Abc_NtkObjNumMax(pNtk) + 1);

  // 初始化：PI 的 cut 就是 {PI}
  for (Abc_Obj_t* pi : pis) {
    std::vector<int> c{ ID(pi) };
    nodeCuts[ID(pi)].insert(c);
  }
  // AND 的 trivial cut {v} 也加入（會被 |R(S)|>=l 自然濾掉）
  for (Abc_Obj_t* v : ands) {
    std::vector<int> c{ ID(v) };
    nodeCuts[ID(v)].insert(c);
  }

  // 自底向上枚舉：對每個 AND v，合併左右子 cuts
  for (Abc_Obj_t* v : ands) {
    Abc_Obj_t* a = Abc_ObjFanin0(v);
    Abc_Obj_t* b = Abc_ObjFanin1(v);
    auto& Ca = nodeCuts[ID(a)];
    auto& Cb = nodeCuts[ID(b)];
    auto& Cv = nodeCuts[ID(v)];

    for (auto const& c0 : Ca) {
      for (auto const& c1 : Cb) {
        std::vector<int> u; u.reserve(c0.size() + c1.size());
        // 合併（有序）
        std::merge(c0.begin(), c0.end(), c1.begin(), c1.end(), std::back_inserter(u));
        u.erase(std::unique(u.begin(), u.end()), u.end());
        // irredundant（刪掉祖先葉）
        MakeIrredundant(u, pNtk);
        if ((int)u.size() <= k) Cv.insert(u);
      }
    }
  }

  // 彙整：葉集合 S -> roots（AND 節點）集合
  std::unordered_map<std::vector<int>, std::set<int>, VecHash, VecEq> S2roots;
  for (Abc_Obj_t* v : ands) {
    int vid = ID(v);
    for (auto const& S : nodeCuts[vid]) {
      // 略過單葉 trivial cut（不會成為 multi-output）
      if ((int)S.size() == 1 && S[0] == vid) continue;
      S2roots[S].insert(vid);
    }
  }

  // 輸出：只印 |R(S)| >= l
  for (auto const& kv : S2roots) {
    auto const& S = kv.first;
    auto const& R = kv.second;
    if ((int)R.size() < l) continue;

    // 左側：葉（升冪）
    for (size_t t = 0; t < S.size(); ++t) {
      if (t) Abc_Print(1, " ");
      Abc_Print(1, "%d", S[t]);
    }
    Abc_Print(1, " :");

    // 右側：roots（升冪，std::set 已排序）
    for (int rid : R) Abc_Print(1, " %d", rid);
    Abc_Print(1, "\n");
  }

  return 0;
}

// ---- 註冊這個新指令（保留你原本的 lsv_print_nodes 也行） ----
static void Lsv_Init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut_3", Lsv_CommandPrintMoCut, 0);
}

static void Lsv_Destroy(Abc_Frame_t* /*pAbc*/) { }

Abc_FrameInitializer_t frameInit_mocut = { Lsv_Init, Lsv_Destroy };

struct LsvMoCutPackageReg {
  LsvMoCutPackageReg() { Abc_FrameAddInitializer(&frameInit_mocut); }
} g_lsvMoCutPackageReg;