// src/ext-lsv/lsvCmd.cpp
//
// PA1 Problem 4: lsv_printmocut <k> <l>
// - Enumerate irredundant k-feasible cuts for every PI/AND (NOT CO)
// - Group outputs sharing the same leaf set L (|L| <= k)
// - Print lines "leaf_ids... : out_ids..." (both sides strictly ascending)
//
// Minimal corrections applied:
//   * nodeCuts sized to N+1 (IDs are 1-based)
//   * CONST1 has exactly one cut: {} (never a leaf)
//   * Deterministic output (sorted groups, sorted outs)
//   * No dummy "lsv" command registration

extern "C" {
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "aig/aig/aig.h"
}

#include <algorithm>
#include <string>
#include <sstream>
#include <vector>
#include <unordered_map>
#include <utility>

// --------------------------- Utilities ---------------------------

static std::string joinInts(const std::vector<int>& v, const char* sep = " ") {
    std::ostringstream oss;
    for (size_t i = 0; i < v.size(); ++i) {
        if (i) oss << sep;
        oss << v[i];
    }
    return oss.str();
}

// a ⊆ b  (both vectors must be strictly ascending)
static bool is_subset_of(const std::vector<int>& a, const std::vector<int>& b) {
    if (a.size() > b.size()) return false;
    size_t i = 0, j = 0;
    while (i < a.size() && j < b.size()) {
        if (a[i] == b[j]) { ++i; ++j; }
        else if (a[i] > b[j]) { ++j; }
        else { return false; }
    }
    return i == a.size();
}

// Insert `cut` iff not dominated; prune supersets.
// All cuts kept sorted & unique.
static void push_cut_unique_dominated(std::vector<std::vector<int>>& cuts, std::vector<int> cut) {
    std::sort(cut.begin(), cut.end());
    cut.erase(std::unique(cut.begin(), cut.end()), cut.end());

    // reject exact dup
    for (auto const& c : cuts) {
        if (c.size() == cut.size() && std::equal(c.begin(), c.end(), cut.begin()))
            return;
    }
    // if some existing c ⊆ cut, then cut is dominated
    for (auto const& c : cuts) {
        if (is_subset_of(c, cut)) return;
    }
    // remove supersets of cut
    cuts.erase(std::remove_if(cuts.begin(), cuts.end(),
                              [&](std::vector<int> const& c){ return is_subset_of(cut, c); }),
               cuts.end());
    cuts.push_back(std::move(cut));
}

// ------------------------- Core command --------------------------

static int Cmd_LsvPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv)
{
    // Args: lsv_printmocut <k> <l>
    if (argc != 3) {
        Abc_Print(-1, "usage: lsv_printmocut <k> <l>\n");
        Abc_Print(-1, "  k: max leaf-set size (3..6),  l: minimum outputs per group (1..4)\n");
        return 1;
    }
    int K = atoi(argv[1]);
    int Lmin = atoi(argv[2]);
    if (K < 3 || K > 6 || Lmin < 1 || Lmin > 4) {
        Abc_Print(-1, "Error: k must be in [3,6], l in [1,4].\n");
        return 1;
    }

    // Preconditions
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Error: empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk) || !Abc_NtkHasAig(pNtk)) {
        Abc_Print(-1, "Error: please run \"strash\" first (AIG required).\n");
        return 1;
    }

    // Per-node cuts: index by Abc_ObjId (1-based) → size +1
    int nObjs = Abc_NtkObjNum(pNtk);
    std::vector<std::vector<std::vector<int>>> nodeCuts(nObjs + 1);

    // Seed CONST1 with the empty cut {} (never appears as a leaf)
    Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
    if (pConst) {
        nodeCuts[ Abc_ObjId(pConst) ].push_back(std::vector<int>{});
    }

    // Build cuts bottom-up by ABC object order:
    // const(0), then CIs, then COs, then ANDs (topologically sorted).
    Abc_Obj_t* pObj; int i;
    Abc_NtkForEachObj(pNtk, pObj, i) {
        if (!pObj) continue;

        // Skip COs as "nodes to build cuts for"
        if (Abc_ObjIsCo(pObj)) continue;

        int vId = Abc_ObjId(pObj);
        auto& cutsV = nodeCuts[vId];

        // Skip trivial {v} for CONST1 (we already seeded {} above)
        if (pObj != pConst) {
            std::vector<int> triv{ vId };
            push_cut_unique_dominated(cutsV, std::move(triv));
        }

        // Combine fanin cuts for AND nodes only
        if (Abc_AigNodeIsAnd(pObj)) {
            Abc_Obj_t* pF0 = Abc_ObjRegular(Abc_ObjFanin0(pObj));
            Abc_Obj_t* pF1 = Abc_ObjRegular(Abc_ObjFanin1(pObj));
            int id0 = Abc_ObjId(pF0);
            int id1 = Abc_ObjId(pF1);

            auto const& cuts0 = nodeCuts[id0];
            auto const& cuts1 = nodeCuts[id1];

            for (auto const& c0 : cuts0) {
                for (auto const& c1 : cuts1) {
                    std::vector<int> merged;
                    merged.reserve(c0.size() + c1.size());
                    std::merge(c0.begin(), c0.end(), c1.begin(), c1.end(), std::back_inserter(merged));
                    merged.erase(std::unique(merged.begin(), merged.end()), merged.end());
                    if ((int)merged.size() > K) continue;
                    push_cut_unique_dominated(cutsV, std::move(merged));
                }
            }
        }
    }

    // Group outputs sharing identical leaf sets.
    // Outputs = CIs (PIs) + AND nodes; COs excluded.
    struct VecHash {
        size_t operator()(std::vector<int> const& v) const noexcept {
            size_t h = 1469598103934665603ull; // FNV-1a
            for (int x : v) { h ^= (size_t)x; h *= 1099511628211ull; }
            return h;
        }
    };
    struct VecEq {
        bool operator()(std::vector<int> const& a, std::vector<int> const& b) const noexcept {
            return a.size() == b.size() && std::equal(a.begin(), a.end(), b.begin());
        }
    };

    std::unordered_map<std::vector<int>, std::vector<int>, VecHash, VecEq> group;

    // Add PI outputs
    Abc_NtkForEachCi(pNtk, pObj, i) {
        int id = Abc_ObjId(pObj);
        for (auto const& L : nodeCuts[id]) {
            if ((int)L.size() > K) continue;
            if (L.empty()) continue; // safety: do not emit empty leaves
            group[L].push_back(id);
        }
    }
    // Add AND outputs
    Abc_NtkForEachObj(pNtk, pObj, i) {
        if (!Abc_AigNodeIsAnd(pObj)) continue;
        int id = Abc_ObjId(pObj);
        for (auto const& L : nodeCuts[id]) {
            if ((int)L.size() > K) continue;
            if (L.empty()) continue;
            group[L].push_back(id);
        }
    }

    // Collect, filter (|outs| >= l), and sort deterministically
    std::vector<std::pair<std::vector<int>, std::vector<int>>> results;
    results.reserve(group.size());
    for (auto& kv : group) {
        auto leaves = kv.first;   // copy
        auto outs   = kv.second;  // copy
        if ((int)outs.size() < Lmin) continue;
        std::sort(outs.begin(), outs.end());
        outs.erase(std::unique(outs.begin(), outs.end()), outs.end());
        results.emplace_back(std::move(leaves), std::move(outs));
    }

    std::sort(results.begin(), results.end(),
              [](auto const& a, auto const& b) {
                  if (a.first != b.first) return a.first < b.first;
                  return a.second < b.second;
              });

    // Print results (no banner when empty)
    for (auto const& it : results) {
        Abc_Print(1, "%s : %s\n",
                  joinInts(it.first).c_str(),
                  joinInts(it.second).c_str());
    }

    return 0;
}

// -------------------------- Initializer --------------------------

extern "C" void Lsv_Init(Abc_Frame_t* pAbc)
{
    // Register only the required command
    Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Cmd_LsvPrintMoCut, 0);
}
