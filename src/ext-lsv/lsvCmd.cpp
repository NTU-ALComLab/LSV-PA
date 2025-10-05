// src/ext-lsv/lsvCmd.cpp  —— 只保留「我的版本」語意：PI + AND 都算輸出節點
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"

#include <algorithm>
#include <map>
#include <vector>
#include <set>
#include <cstdio>
#include <cstdlib>

// ------------------ 共用型別/工具 ------------------
using Cut     = std::vector<int>;
using CutList = std::vector<Cut>;

static inline bool IsConst1(Abc_Ntk_t* pNtk, Abc_Obj_t* pObj) {
    return pObj == Abc_AigConst1(pNtk);
}

static inline void sort_unique(Cut& v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

static inline Cut union_cuts(const Cut& a, const Cut& b) {
    Cut u; u.reserve(a.size() + b.size());
    std::set_union(a.begin(), a.end(), b.begin(), b.end(), std::back_inserter(u));
    return u;
}

static inline bool is_subset_of(const Cut& a, const Cut& b) {
    if (a.size() > b.size()) return false;
    size_t i = 0, j = 0;
    while (i < a.size() && j < b.size()) {
        if (a[i] == b[j]) { ++i; ++j; }
        else if (a[i] > b[j]) { ++j; }
        else { return false; } // a[i] < b[j]，a 有元素不在 b
    }
    return i == a.size();
}

static void make_irredundant(CutList& cuts) {
    for (auto& c : cuts) sort_unique(c);
    std::sort(cuts.begin(), cuts.end());
    cuts.erase(std::unique(cuts.begin(), cuts.end()), cuts.end());

    std::vector<char> keep(cuts.size(), 1);
    for (size_t i = 0; i < cuts.size(); ++i) if (keep[i]) {
        for (size_t j = 0; j < cuts.size(); ++j) if (i != j && keep[j]) {
            if (cuts[j].size() < cuts[i].size() && is_subset_of(cuts[j], cuts[i])) {
                keep[i] = 0; break;
            }
        }
    }
    CutList pruned; pruned.reserve(cuts.size());
    for (size_t i = 0; i < cuts.size(); ++i) if (keep[i]) pruned.push_back(std::move(cuts[i]));
    cuts.swap(pruned);
}

// ------------------ 列舉每個節點的 irredundant k-cuts ------------------
static std::vector<CutList> enumerate_irredundant_cuts(Abc_Ntk_t* pNtk, int k) {
    const int maxId = Abc_NtkObjNumMax(pNtk);
    std::vector<CutList> nodeCuts(maxId + 1);

    Abc_Obj_t* pObj; int i;
    // strash 後 ID = 拓撲序：Const0 -> PIs -> POs -> AND nodes
    Abc_NtkForEachObj(pNtk, pObj, i) {
        if (!pObj) continue;
        if (Abc_ObjIsPo(pObj)) continue; // d 小題忽略 PO

        const int id = Abc_ObjId(pObj);

        // SI（Const1/PI）: { {id} }
        if (IsConst1(pNtk, pObj) || Abc_ObjIsPi(pObj)) {
            nodeCuts[id] = { Cut{ id } };
            continue;
        }

        // AND node
        if (Abc_ObjIsNode(pObj)) {
            Abc_Obj_t* f0 = Abc_ObjFanin0(pObj);
            Abc_Obj_t* f1 = Abc_ObjFanin1(pObj);
            const int id0 = Abc_ObjId(f0);
            const int id1 = Abc_ObjId(f1);

            CutList cand;
            // {i}
            cand.push_back(Cut{ id });

            // {fanin0, fanin1}
            {
                Cut pair = { id0, id1 };
                sort_unique(pair);
                if (k <= 0 || (int)pair.size() <= k) cand.push_back(std::move(pair));
            }

            // fanin 的 cut 兩兩聯集
            const CutList& c0 = nodeCuts[id0];
            const CutList& c1 = nodeCuts[id1];
            for (const auto& a : c0)
            for (const auto& b : c1) {
                Cut u = union_cuts(a, b);
                if (k <= 0 || (int)u.size() <= k) cand.push_back(std::move(u));
            }

            make_irredundant(cand);
            nodeCuts[id] = std::move(cand);
        }
    }
    return nodeCuts;
}

// ------------------ 列印 multi-output cuts（PI + AND 都算輸出節點） ------------------
static void print_mocuts(Abc_Ntk_t* pNtk, int k, int l) {
    auto allCuts = enumerate_irredundant_cuts(pNtk, k);

    // cut -> 被哪些輸出節點（PI 或 AND）共享
    std::map<Cut, std::vector<int>> cut2outs;
    Abc_Obj_t* p; int i;
    Abc_NtkForEachObj(pNtk, p, i) {
        if (!p) continue;
        if (!(Abc_ObjIsPi(p) || Abc_ObjIsNode(p))) continue; // 只統計 PI 與 AND
        const int id = Abc_ObjId(p);
        for (const auto& c : allCuts[id]) cut2outs[c].push_back(id);
    }

    for (auto& kv : cut2outs) {
        const Cut& inCut = kv.first;
        auto& outs = kv.second;

        std::sort(outs.begin(), outs.end());
        outs.erase(std::unique(outs.begin(), outs.end()), outs.end());

        if ((int)inCut.size() > k) continue;
        if ((int)outs.size() < l) continue;

        for (size_t t = 0; t < inCut.size(); ++t)
            Abc_Print(1, "%d%s", inCut[t], (t + 1 == inCut.size()) ? "" : " ");
        Abc_Print(1, " : ");
        for (size_t t = 0; t < outs.size(); ++t)
            Abc_Print(1, "%d%s", outs[t], (t + 1 == outs.size()) ? "" : " ");
        Abc_Print(1, "\n");
    }
}

// ------------------ 指令 handler（兩個名字同一實作） ------------------
static int Cmd_PrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
    if (argc < 3) { Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n"); return 1; }
    int k = std::max(1, atoi(argv[1]));
    int l = std::max(1, atoi(argv[2]));

    // 自動 strash（checker 餵 .blif 也安全）
    Cmd_CommandExecute(pAbc, "strash");

    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk || !Abc_NtkIsStrash(pNtk)) { Abc_Print(-1, "Error: not AIG.\n"); return 1; }

    print_mocuts(pNtk, k, l);
    return 0;
}

// ------------------ 註冊 & 初始化保底 ------------------
extern "C" ABC_DLL void init(Abc_Frame_t* pAbc) {
    Abc_Print(1, "[LSV] ext-lsv loaded\n");
    // 兩個指令名都走同一套「我的版本」語意
    Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut",   Cmd_PrintMoCut, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut_2", Cmd_PrintMoCut, 0);
}
extern "C" ABC_DLL void destroy(Abc_Frame_t*) {}
extern "C" ABC_DLL Abc_FrameInitializer_t frame_initializer = { init, destroy };

// 保底：在某些連結/最佳化情況下也能確保 initializer 被註冊
static void Lsv_ForceRegisterInitializer(void) __attribute__((constructor));
static void Lsv_ForceRegisterInitializer(void) { Abc_FrameAddInitializer(&frame_initializer); }
