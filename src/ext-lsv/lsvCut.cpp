#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <algorithm>
#include <functional>

// ABC headers
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"
#include "misc/vec/vec.h"

// Use a C++ anonymous namespace to limit the scope of helper functions and variables
namespace {

// Forward declarations of static functions
static int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv);
void Lsv_NtkEnumerateAndPrintMocut(Abc_Ntk_t* pNtk, int k, int l);

// Function to register the command
void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMocut, 0);
}

// Function to be called upon exit
void destroy(Abc_Frame_t* pAbc) {}

// ABC frame initializer
Abc_FrameInitializer_t frame_initializer = {init, destroy};

// Package registration manager
struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;


// A map for memoization to store computed cuts for each node.
// Key: Node ID, Value: A vector of cuts, where each cut is a sorted vector of node IDs.
std::map<int, std::vector<std::vector<int>>> g_memo;

// Recursive function to find all k-feasible cuts for a given node.
const std::vector<std::vector<int>>& find_cuts_recursive(Abc_Obj_t* pNode, int k) {
    int nodeId = Abc_ObjId(pNode);

    if (g_memo.count(nodeId)) {
        return g_memo.at(nodeId);
    }

    if (Abc_ObjIsCi(pNode)) {
        g_memo[nodeId] = {{nodeId}};
        return g_memo.at(nodeId);
    }

    if (Abc_ObjIsNode(pNode)) {
        std::vector<std::vector<int>> this_node_cuts;
        this_node_cuts.push_back({nodeId});

        const auto& fanin0_cuts = find_cuts_recursive(Abc_ObjFanin0(pNode), k);
        const auto& fanin1_cuts = find_cuts_recursive(Abc_ObjFanin1(pNode), k);

        for (const auto& c1 : fanin0_cuts) {
            for (const auto& c2 : fanin1_cuts) {
                std::vector<int> merged_cut;
                merged_cut.reserve(c1.size() + c2.size());
                std::merge(c1.begin(), c1.end(), c2.begin(), c2.end(),
                           std::back_inserter(merged_cut));
                merged_cut.erase(std::unique(merged_cut.begin(), merged_cut.end()), merged_cut.end());

                if ((int)merged_cut.size() > k) {
                    continue;
                }

                bool is_dominated = false;
                std::vector<std::vector<int>> next_gen_cuts;
                for (const auto& existing_cut : this_node_cuts) {
                    if (std::includes(merged_cut.begin(), merged_cut.end(),
                                      existing_cut.begin(), existing_cut.end())) {
                        is_dominated = true;
                        break;
                    }
                    if (!std::includes(existing_cut.begin(), existing_cut.end(),
                                       merged_cut.begin(), merged_cut.end())) {
                        next_gen_cuts.push_back(existing_cut);
                    }
                }

                if (!is_dominated) {
                    next_gen_cuts.push_back(merged_cut);
                    this_node_cuts = next_gen_cuts;
                }
            }
        }
        g_memo[nodeId] = this_node_cuts;
        return g_memo.at(nodeId);
    }
    
    static const std::vector<std::vector<int>> empty_result;
    return empty_result;
}


// Main logic to enumerate and print multi-output cuts.
void Lsv_NtkEnumerateAndPrintMocut(Abc_Ntk_t* pNtk, int k, int l) {
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "The network is not a structurally hashed AIG. Please run 'strash'.\n");
        return;
    }

    g_memo.clear();
    std::map<std::vector<int>, std::vector<int>> multi_output_cuts;

    Abc_Obj_t* pObj;
    int i;
    
    Vec_Ptr_t* vNodes = Abc_AigGetLevelizedOrder(pNtk, 1);
    
    // ** FINAL FIX: Add a NULL check before using the object pointer **
    for (i = 0; i < Vec_PtrSize(vNodes); i++)
    {
        pObj = (Abc_Obj_t *)Vec_PtrEntry(vNodes, i);
        if (pObj == NULL) {
            continue;
        }
        if (Abc_ObjIsCi(pObj) || Abc_ObjIsNode(pObj)) {
            find_cuts_recursive(pObj, k);
        }
    }
    Vec_PtrFree(vNodes);

    for (const auto& pair : g_memo) {
        int output_node_id = pair.first;
        const auto& cuts = pair.second;
        for (const auto& cut : cuts) {
            multi_output_cuts[cut].push_back(output_node_id);
        }
    }

    for (auto const& [cut_nodes, output_nodes] : multi_output_cuts) {
        if ((int)output_nodes.size() >= l) {
            std::vector<int> sorted_outputs = output_nodes;
            std::sort(sorted_outputs.begin(), sorted_outputs.end());

            for (size_t i = 0; i < cut_nodes.size(); ++i) {
                printf("%d%c", cut_nodes[i], (i == cut_nodes.size() - 1) ? ' ' : ' ');
            }
            printf(": ");
            for (size_t i = 0; i < sorted_outputs.size(); ++i) {
                printf("%d%c", sorted_outputs[i], (i == sorted_outputs.size() - 1) ? '\n' : ' ');
            }
        }
    }
}


// The command function callable from the ABC framework.
int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv) {
    int k = 0, l = 0;
    int c;
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    if (argc - globalUtilOptind < 2) {
        goto usage;
    }

    k = atoi(argv[globalUtilOptind]);
    l = atoi(argv[globalUtilOptind + 1]);

    if (!(k >= 3 && k <= 6 && l >= 1 && l <= 4)) {
        Abc_Print(-1, "Error: k must be in [3, 6] and l must be in [1, 4].\n");
        goto usage;
    }

    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }

    Lsv_NtkEnumerateAndPrintMocut(pNtk, k, l);

    return 0;

usage:
    Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
    Abc_Print(-2, "\t        enumerates and prints k-l multi-output cuts in an AIG\n");
    Abc_Print(-2, "\t<k>   : the maximum size of a cut (3 <= k <= 6)\n");
    Abc_Print(-2, "\t<l>   : the minimum number of outputs for a cut (1 <= l <= 4)\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}

} // end anonymous namespace