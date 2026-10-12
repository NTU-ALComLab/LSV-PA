#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iterator>
#include <map>
#include <vector>
#include <string>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

const bool REMOVE_DOMINATED = false; // Set to true for minimal cuts

bool is_subset(const std::vector<int>& a, const std::vector<int>& b) {
    return std::includes(b.begin(), b.end(), a.begin(), a.end());
}

// Generate k-feasible cuts for the network
void compute_cuts(Abc_Ntk_t* ntk, int k, std::vector<std::vector<std::vector<int>>>& all_cuts) {
    all_cuts.assign(Abc_NtkObjNumMax(ntk), std::vector<std::vector<int>>());
    Abc_Obj_t* obj;
    int i;

    all_cuts[Abc_ObjId(Abc_AigConst1(ntk))].push_back({}); // Constant node

    // Primary inputs
    Abc_NtkForEachCi(ntk, obj, i) {
        all_cuts[Abc_ObjId(obj)].push_back({(int)Abc_ObjId(obj)});
    }

    // Internal nodes (AND gates)
    Abc_NtkForEachNode(ntk, obj, i) {
        int id = Abc_ObjId(obj);
        auto& my_cuts = all_cuts[id];
        my_cuts.push_back({id}); // Trivial cut

        const auto& c0 = all_cuts[Abc_ObjId(Abc_ObjFanin0(obj))];
        const auto& c1 = all_cuts[Abc_ObjId(Abc_ObjFanin1(obj))];

        for (const auto& cut0 : c0) {
            for (const auto& cut1 : c1) {
                std::vector<int> merged;
                std::set_union(cut0.begin(), cut0.end(), cut1.begin(), cut1.end(), std::back_inserter(merged));
                
                if ((int)merged.size() > k) continue;
                if (std::find(my_cuts.begin(), my_cuts.end(), merged) != my_cuts.end()) continue;

                if (REMOVE_DOMINATED) {
                    bool dominated = false;
                    for (size_t t = 1; t < my_cuts.size() && !dominated; ++t) {
                        if (is_subset(my_cuts[t], merged)) dominated = true;
                    }
                    if (dominated) continue;
                    
                    for (size_t t = my_cuts.size(); t-- > 1;) {
                        if (is_subset(merged, my_cuts[t])) my_cuts.erase(my_cuts.begin() + t);
                    }
                }
                my_cuts.push_back(merged);
            }
        }
    }
}

// Evaluate truth table recursively
uint64_t get_tt_val(Abc_Obj_t* node, std::map<int, uint64_t>& cache) {
    int id = Abc_ObjId(node);
    if (cache.count(id)) return cache[id];

    uint64_t val = 0;
    if (Abc_ObjType(node) == ABC_OBJ_CONST1) {
        val = ~0ULL;
    } else if (Abc_ObjIsNode(node)) {
        uint64_t left = get_tt_val(Abc_ObjFanin0(node), cache);
        uint64_t right = get_tt_val(Abc_ObjFanin1(node), cache);
        
        if (Abc_ObjFaninC0(node)) left = ~left;
        if (Abc_ObjFaninC1(node)) right = ~right;
        
        val = left & right;
    }
    
    cache[id] = val;
    return val;
}

uint64_t calc_cut_truth_table(Abc_Ntk_t* ntk, int root_id, const std::vector<int>& cut) {
    int k = cut.size();
    std::map<int, uint64_t> cache;
    
    for (int i = 0; i < k; ++i) {
        uint64_t mask = 0;
        for (int idx = 0; idx < (1 << k); ++idx) {
            if ((idx >> (k - 1 - i)) & 1) mask |= (1ULL << idx);
        }
        cache[cut[i]] = mask;
    }

    uint64_t tt = get_tt_val(Abc_NtkObj(ntk, root_id), cache);
    if (k < 6) {
        tt &= ((1ULL << (1 << k)) - 1ULL);
    }
    return tt;
}

// Evaluate BDD recursively
DdNode* build_bdd(DdManager* dd, Abc_Obj_t* node, std::map<int, DdNode*>& cache, std::vector<DdNode*>& tracked_nodes) {
    int id = Abc_ObjId(node);
    if (cache.count(id)) return cache[id];

    DdNode* res = nullptr;
    if (Abc_ObjType(node) == ABC_OBJ_CONST1) {
        res = Cudd_ReadOne(dd);
    } else if (Abc_ObjIsNode(node)) {
        DdNode* left = build_bdd(dd, Abc_ObjFanin0(node), cache, tracked_nodes);
        DdNode* right = build_bdd(dd, Abc_ObjFanin1(node), cache, tracked_nodes);
        
        if (Abc_ObjFaninC0(node)) left = Cudd_Not(left);
        if (Abc_ObjFaninC1(node)) right = Cudd_Not(right);
        
        res = Cudd_bddAnd(dd, left, right);
        Cudd_Ref(res);
        tracked_nodes.push_back(res);
    } else {
        res = Cudd_ReadLogicZero(dd); 
    }
    
    cache[id] = res;
    return res;
}

int calc_bdd_size(DdManager* dd, Abc_Ntk_t* ntk, int root_id, const std::vector<int>& cut) {
    std::map<int, DdNode*> cache;
    std::vector<DdNode*> tracked_nodes;
    
    for (size_t i = 0; i < cut.size(); ++i) {
        cache[cut[i]] = Cudd_bddIthVar(dd, (int)i);
    }
    
    DdNode* root_bdd = build_bdd(dd, Abc_NtkObj(ntk, root_id), cache, tracked_nodes);
    int size = Cudd_DagSize(root_bdd);
    
    for (auto* n : tracked_nodes) {
        Cudd_RecursiveDeref(dd, n);
    }
    
    return size;
}

int process_cuts(Abc_Frame_t* abc_frame, int argc, char** argv, bool is_bdd) {
    Abc_Ntk_t* ntk = Abc_FrameReadNtk(abc_frame);
    std::string cmd_name = is_bdd ? "lsv_cut_bddsize" : "lsv_cut_tt";
    int max_k = is_bdd ? 64 : 6;

    if (argc != 2 || std::string(argv[1]) == "-h") {
        Abc_Print(-2, "usage: %s <k>\n", cmd_name.c_str());
        return 1;
    }

    int k = atoi(argv[1]);
    if (k < 1 || k > max_k) {
        Abc_Print(-2, "Invalid k. Must be between 1 and %d\n", max_k);
        return 1;
    }
    if (!ntk) {
        Abc_Print(-1, "Error: Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(ntk)) {
        Abc_Print(-1, "Error: Network is not an AIG. Run 'strash' first.\n");
        return 1;
    }

    std::vector<std::vector<std::vector<int>>> all_cuts;
    compute_cuts(ntk, k, all_cuts);

    DdManager* dd = nullptr;
    if (is_bdd) {
        dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    }

    Abc_Obj_t* obj;
    int i;
    Abc_NtkForEachNode(ntk, obj, i) {
        int id = Abc_ObjId(obj);
        for (const auto& cut : all_cuts[id]) {
            // Print the cut
            printf("%d: ", id);
            for (size_t j = 0; j < cut.size(); ++j) {
                printf(j == 0 ? "%d" : " %d", cut[j]);
            }
            printf(": ");

            // Print the corresponding output
            if (is_bdd) {
                printf("%d\n", calc_bdd_size(dd, ntk, id, cut));
            } else {
                printf("%llX\n", (unsigned long long)calc_cut_truth_table(ntk, id, cut));
            }
        }
    }

    if (dd) Cudd_Quit(dd);
    return 0;
}

int cmd_cut_tt(Abc_Frame_t* abc_frame, int argc, char** argv) {
    return process_cuts(abc_frame, argc, argv, false);
}

int cmd_cut_bddsize(Abc_Frame_t* abc_frame, int argc, char** argv) {
    return process_cuts(abc_frame, argc, argv, true);
}

// Extension Registration
void init_lsv_cmds(Abc_Frame_t* abc_frame) {
    Cmd_CommandAdd(abc_frame, "LSV", "lsv_cut_tt", cmd_cut_tt, 0);
    Cmd_CommandAdd(abc_frame, "LSV", "lsv_cut_bddsize", cmd_cut_bddsize, 0);
}

void destroy_lsv_cmds(Abc_Frame_t* abc_frame) {}

Abc_FrameInitializer_t lsv_initializer = {init_lsv_cmds, destroy_lsv_cmds};

struct LsvRegistration {
    LsvRegistration() {
        Abc_FrameAddInitializer(&lsv_initializer);
    }
} lsv_registration_manager;