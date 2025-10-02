// src/ext-lsv/lsvCmd.cpp
//
// PA1 Problem 4: lsv_printmocut <k> <l>
// - Enumerate irredundant k-feasible cuts for every PI/AND (NOT CO)
// - Group outputs sharing the same leaf set L (|L| <= k)
// - Print lines "leaf_ids... : out_ids..." (both sides strictly ascending)
// Implementation details:
//   * Build cuts bottom-up in topological order (PIs -> ANDs)
//   * CONST1 has exactly one cut: {} (never appears as a leaf)
//   * Irredundancy via dominance: keep only set-minimal cuts
//   * Deterministic final ordering of lines

#include "base/abc/abc.h"
#include "aig/aig/aig.h"

#include <algorithm>
#include <string>
#include <sstream>
#include <vector>
#include <unordered_map>
#include <utility>

////////////////////////////////////////////////////////////////////////
// Small utilities
////////////////////////////////////////////////////////////////////////

static std::string joinInts(const std::vector<int>& v, const char* sep = " ") {
    std::ostringstream oss;
    for (size_t i = 0; i < v.size(); ++i) {
        if (i) oss << sep;
        oss << v[i];
    }
    return oss.str();
}

// Return true if a ⊆ b (both MUST be sorted strictly ascending)
static bool is_subset_of(const std::vector<int>& a, const std::vector<int>& b) {
    if (a.size() > b.size()) return false;
    size_t i = 0, j = 0;
    while (i < a.size() && j < b.size()) {
        if (a[i] == b[j]) { ++i; ++j; }
        else if (a[i] > b[j]) { ++j; }
        else { return false; } // a[i] not found in b
    }
    return i == a.size();
}

// Insert `cut` into `cuts` if it is not dominated by existing cuts.
// Remove any existing cuts that are supersets of `cut`.
// All cuts MUST remain sorted unique vectors.
static void push_cut_unique_dominated(std::vector<std::vector<int>>& cuts, std::vector<int> cut) {
    // Ensure ascending & unique inside the vector
    std::sort(cut.begin(), cut.end());
    cut.erase(std::unique(cut.begin(), cut.end()), cut.end());

    // Reject exact duplicates
    for (auto const& c : cuts) {
        if (c.size() == cut.size() && std::equal(c.begin(), c.end(), cut.begin()))
            return;
    }
    // If any existing cut is subset of `cut`, then `cut` is dominated -> reject
    for (auto const& c : cuts) {
        if (is_subset_of(c, cut)) return;
    }
    // Remove any existing cuts that are supersets of `cut`
    cuts.erase(std::remove_if(cuts.begin(), cuts.end(),
                              [&](std::vector<int> const& c){ return is_subset_of(cut, c); }),
               cuts.end());
    // Insert
    cuts.push_back(std::move(cut));
}

////////////////////////////////////////////////////////////////////////
// Core command
////////////////////////////////////////////////////////////////////////

static int Cmd_LsvPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv)
{
    // ----------------------------------------------------------------
    // Parse arguments: lsv_printmocut <k> <l>
    // ----------------------------------------------------------------
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

    // ----------------------------------------------------------------
    // Network preconditions
    // ----------------------------------------------------------------
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Error: empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk) || !Abc_NtkHasAig(pNtk)) {
        Abc_Print(-1, "Error: please run \"strash\" first (AIG required).\n");
        return 1;
    }

    // ----------------------------------------------------------------
    // Storage for per-node cuts: index by Abc_ObjId (1-based). Size +1.
    // Each entry is a vector of cuts; each cut is a sorted vector<int> of leaf IDs.
    // ----------------------------------------------------------------
    int nMax = Abc_NtkObjNum(pNtk) + 1;
    std::vector<std::vector<std::vector<int>>> nodeCuts(nMax);

    // Seed CONST1 with the empty cut {} (never as a leaf)
    Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
    if (pConst) {
        nodeCuts[ Abc_ObjId(pConst) ].push_back(std::vector<int>{});
    }

    // PIs: only the trivial cut {pi}
    Abc_Obj_t* pObj; int i;
    Abc_NtkForEachCi(pNtk, pObj, i) {
        int id = Abc_ObjId(pObj);
        nodeCuts[id].push_back(std::vector<int>{ id });
    }

    // ANDs in topological order: combine fanin cuts
    Abc_AigForEachAnd(pNtk, pObj, i) {
        int v   = Abc_ObjId(pObj);
        Abc_Obj_t* pF0 = Abc_ObjRegular(Abc_ObjFanin0(pObj));
        Abc_Obj_t* pF1 = Abc_ObjRegular(Abc_ObjFanin1(pObj));
        int id0 = Abc_ObjId(pF0);
        int id1 = Abc_ObjId(pF1);

        auto& cutsV = nodeCuts[v];

        // Trivial cut {v} (standard for node-cuts)
        push_cut_unique_dominated(cutsV, std::vector<int>{ v });

        auto const& cuts0 = nodeCuts[id0];
        auto const& cuts1 = nodeCuts[id1];

        for (auto const& c0 : cuts0) {
            for (auto const& c1 : cuts1) {
                // merge two sorted leaf vectors
                std::vector<int> merged;
                merged.reserve(c0.size() + c1.size());
                std::merge(c0.begin(), c0.end(), c1.begin(), c1.end(), std::back_inserter(merged));
                merged.erase(std::unique(merged.begin(), merged.end()), merged.end());
                if ((int)merged.size() > K) continue; // respect k
                push_cut_unique_dominated(cutsV, std::move(merged));
            }
        }
    }

    // ----------------------------------------------------------------
    // Group outputs sharing identical leaf sets:
    // Outputs = PIs (CIs) + AND nodes; exclude COs
    // We store groups in a map keyed by the leaf vector itself.
    // ----------------------------------------------------------------
    struct VecHash {
        size_t operator()(std::vector<int> const& v) const noexcept {
            // simple 64-bit FNV-1a on ints
            size_t h = 1469598103934665603ull;
            for (int x : v) {
                h ^= (size_t)x;
                h *= 1099511628211ull;
            }
            return h;
        }
    };
    struct VecEq {
        bool operator()(std::vector<int> const& a, std::vector<int> const& b) const noexcept {
            return a.size() == b.size() && std::equal(a.begin(), a.end(), b.begin());
        }
    };

    std::unordered_map<std::vector<int>, std::vector<int>, VecHash, VecEq> group;

    // 1) add PI outputs
    Abc_NtkForEachCi(pNtk, pObj, i) {
        int id = Abc_ObjId(pObj);
        auto const& cuts = nodeCuts[id];
        for (auto const& L : cuts) {
            if ((int)L.size() > K) continue;
            if (L.empty()) continue; // never print empty leaves (safety)
            auto& outs = group[L];
            outs.push_back(id);
        }
    }
    // 2) add AND outputs (topological)
    Abc_AigForEachAnd(pNtk, pObj, i) {
        int id = Abc_ObjId(pObj);
        auto const& cuts = nodeCuts[id];
        for (auto const& L : cuts) {
            if ((int)L.size() > K) continue;
            if (L.empty()) continue; // safety
            auto& outs = group[L];
            outs.push_back(id);
        }
    }

    // ----------------------------------------------------------------
    // Collect, filter (|outs| >= l), and sort deterministically
    // ----------------------------------------------------------------
    std::vector<std::pair<std::vector<int>, std::vector<int>>> results;
    results.reserve(group.size());

    for (auto& kv : group) {
        auto leaves = kv.first;        // copy
        auto outs   = kv.second;       // copy
        std::sort(outs.begin(), outs.end());
        outs.erase(std::unique(outs.begin(), outs.end()), outs.end());
        if ((int)outs.size() >= Lmin) {
            // leaves are already sorted by construction
            results.emplace_back(std::move(leaves), std::move(outs));
        }
    }

    std::sort(results.begin(), results.end(),
              [](auto const& a, auto const& b) {
                  if (a.first != b.first) return a.first < b.first;
                  return a.second < b.second;
              });

    // ----------------------------------------------------------------
    // Print
    // ----------------------------------------------------------------
    for (auto const& it : results) {
        Abc_Print(1, "%s : %s\n",
                  joinInts(it.first).c_str(),
                  joinInts(it.second).c_str());
    }

    return 0;
}

extern "C" void Lsv_Init(Abc_Frame_t* pAbc)
{
    // Register only the required command; no dummy "lsv" command.
    Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Cmd_LsvPrintMoCut, 0);
}
