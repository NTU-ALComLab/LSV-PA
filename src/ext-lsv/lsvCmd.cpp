#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <sstream>
#include <iostream>

extern "C" {
#include "base/abc/abc.h"
#include "base/main/mainInt.h"
#include "base/main/main.h"
#include "aig/aig/aig.h"
}

#include "lsv.h"

// -----------------------------------------------------------------------------
// Forward Declarations
// -----------------------------------------------------------------------------

// Existing PA1 command
static int Cmd_LsvPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);

// PA2 Part 1: BDD unateness command (implemented in lsvUnate.cpp)
extern "C" int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);

// PA2 Part 2: SAT unateness command (implemented in lsvUnateSat.cpp)
extern "C" int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

// -----------------------------------------------------------------------------
// MoCut Utilities (your existing PA1 code)
// -----------------------------------------------------------------------------

static inline bool IsAigNet(Abc_Ntk_t* pNtk) {
    return Abc_NtkIsStrash(pNtk) && Abc_NtkHasAig(pNtk);
}
static inline int ObjId(Abc_Obj_t* pObj) { return Abc_ObjId(pObj); }

// Dominance: return true if A ⊆ B (both sorted).
static bool isSubset(const std::vector<int>& A, const std::vector<int>& B) {
    size_t i = 0, j = 0;
    while (i < A.size() && j < B.size()) {
        if (A[i] == B[j]) { ++i; ++j; }
        else if (A[i] > B[j]) { ++j; }
        else return false;
    }
    return i == A.size();
}

// Stringify a sorted vector<int> with spaces
static std::string joinInts(const std::vector<int>& v) {
    std::ostringstream oss;
    for (size_t i = 0; i < v.size(); ++i) {
        if (i) oss << ' ';
        oss << v[i];
    }
    return oss.str();
}

static int Lsv_PrintMoCut_Run(Abc_Frame_t* pAbc, int K, int L) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) { Abc_Print(-1, "Error: empty network.\n"); return 1; }
    if (!IsAigNet(pNtk)) {
        Abc_Print(-1, "Error: please run \"strash\" to get an AIG first.\n");
        return 1;
    }
    if (K < 3 || K > 6 || L < 1 || L > 4) {
        Abc_Print(-1, "Error: constraints: 3 <= k <= 6 and 1 <= l <= 4.\n");
        return 1;
    }

    const int nObjs = Abc_NtkObjNum(pNtk);
    std::vector<std::vector<std::vector<int>>> nodeCuts(nObjs + 1);

    auto push_cut_unique_dominated = [&](std::vector<std::vector<int>>& cuts, std::vector<int>&& cand) {
        std::sort(cand.begin(), cand.end());
        cand.erase(std::unique(cand.begin(), cand.end()), cand.end());
        for (auto const& c : cuts) if (c == cand) return;
        for (auto const& c : cuts) if (isSubset(c, cand)) return;
        std::vector<std::vector<int>> kept;
        kept.reserve(cuts.size()+1);
        for (auto const& c : cuts) if (!isSubset(cand, c)) kept.push_back(c);
        kept.push_back(std::move(cand));
        cuts.swap(kept);
    };

    Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
    if (pConst) {
        nodeCuts[ObjId(pConst)].push_back(std::vector<int>{});
    }

    Abc_Obj_t* pObj; int i;
    Abc_NtkForEachObj(pNtk, pObj, i) {
        if (!pObj) continue;
        if (Abc_ObjIsCo(pObj)) continue;

        const int vid = ObjId(pObj);
        auto& cutsV = nodeCuts[vid];

        if (pObj != pConst) {
            std::vector<int> triv{ vid };
            push_cut_unique_dominated(cutsV, std::move(triv));
        }

        if (Abc_ObjIsCi(pObj)) continue;

        if (Abc_AigNodeIsAnd(pObj)) {
            Abc_Obj_t* pF0 = Abc_ObjRegular(Abc_ObjFanin0(pObj));
            Abc_Obj_t* pF1 = Abc_ObjRegular(Abc_ObjFanin1(pObj));
            int id0 = ObjId(pF0);
            int id1 = ObjId(pF1);

            auto const& cuts0 = nodeCuts[id0];
            auto const& cuts1 = nodeCuts[id1];

            for (auto const& c0 : cuts0) {
                for (auto const& c1 : cuts1) {
                    std::vector<int> u;
                    u.reserve(c0.size() + c1.size());
                    std::merge(c0.begin(), c0.end(), c1.begin(), c1.end(), std::back_inserter(u));
                    u.erase(std::unique(u.begin(), u.end()), u.end());
                    if ((int)u.size() > K) continue;
                    push_cut_unique_dominated(cutsV, std::move(u));
                }
            }
        }
    }

    struct VecHash {
        size_t operator()(const std::vector<int>& v) const noexcept {
            size_t h = 1469598103934665603ull;
            for (int x : v) { h ^= (size_t)x; h *= 1099511628211ull; }
            return h;
        }
    };
    struct VecEq {
        bool operator()(const std::vector<int>& a, const std::vector<int>& b) const noexcept {
            return a.size() == b.size() && std::equal(a.begin(), a.end(), b.begin());
        }
    };
    std::unordered_map<std::vector<int>, std::vector<int>, VecHash, VecEq> group;

    Abc_NtkForEachCi(pNtk, pObj, i) {
        int oid = ObjId(pObj);
        for (auto const& cut : nodeCuts[oid]) {
            if ((int)cut.size() > K) continue;
            if (cut.empty()) continue;
            group[cut].push_back(oid);
        }
    }
    Abc_NtkForEachObj(pNtk, pObj, i) {
        if (!Abc_AigNodeIsAnd(pObj)) continue;
        int oid = ObjId(pObj);
        for (auto const& cut : nodeCuts[oid]) {
            if ((int)cut.size() > K) continue;
            if (cut.empty()) continue;
            group[cut].push_back(oid);
        }
    }

    std::vector<std::pair<std::vector<int>, std::vector<int>>> results;
    results.reserve(group.size());
    for (auto& kv : group) {
        auto leaves = kv.first;
        auto outs   = kv.second;
        if ((int)outs.size() < L) continue;
        std::sort(outs.begin(), outs.end());
        outs.erase(std::unique(outs.begin(), outs.end()), outs.end());
        results.emplace_back(std::move(leaves), std::move(outs));
    }

    std::sort(results.begin(), results.end(),
              [](auto const& a, auto const& b){
                  if (a.first != b.first) return a.first < b.first;
                  return a.second < b.second;
              });

    for (auto const& it : results) {
        Abc_Print(1, "%s : %s\n",
                  joinInts(it.first).c_str(),
                  joinInts(it.second).c_str());
    }
    return 0;
}

static int Cmd_LsvPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
    int c;
    int K = -1, L = -1;

    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
            default:
                Abc_Print(1, "Usage: %s <k> <l>\n", argv[0]);
                return 0;
        }
    }
    if (argc - globalUtilOptind != 2) {
        Abc_Print(-1, "Error: require exactly 2 positional arguments: <k> <l>\n");
        return 1;
    }
    K = atoi(argv[globalUtilOptind + 0]);
    L = atoi(argv[globalUtilOptind + 1]);
    return Lsv_PrintMoCut_Run(pAbc, K, L);
}

// -----------------------------------------------------------------------------
// Package Initialization
// -----------------------------------------------------------------------------

extern "C" void Lsv_Init(Abc_Frame_t* pAbc) {
    // 1. Existing PA1 command
    Cmd_CommandAdd( pAbc, "LSV", "lsv_printmocut", Cmd_LsvPrintMoCut, 0 );
    
    // 2. PA2 Part 1: BDD unateness
    Cmd_CommandAdd( pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0 );

    // 3. PA2 Part 2: SAT unateness
    Cmd_CommandAdd( pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0 );
    
    // 4. Placeholder
    Cmd_CommandAdd( pAbc, "LSV", "lsv",          nullptr,             0 );
}

extern "C" void Lsv_End(Abc_Frame_t* pAbc) {
    (void)pAbc;
}

extern "C" Abc_FrameInitializer_t Abc_FrameInitializerLsv = {
    /* .init    = */ Lsv_Init,
    /* .destroy = */ Lsv_End
};

namespace {
struct LsvAutoRegistrar {
    LsvAutoRegistrar() {
        Abc_FrameAddInitializer(&Abc_FrameInitializerLsv);
    }
} _lsv_auto_registrar;
} // namespace
