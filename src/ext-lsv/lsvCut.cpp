#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <string>
#include "lsvCut.h"

// A "Cut" is a sorted vector of node IDs.
using Cut = std::vector<int>;
using CutSet = std::set<Cut>;

// Merges two sorted vectors of integers (two cuts) into a new sorted vector removing duplicates.
Cut merge_cuts(const Cut &c1, const Cut &c2)
{
    Cut result;
    result.reserve(c1.size() + c2.size());
    std::merge(c1.begin(), c1.end(), c2.begin(), c2.end(), std::back_inserter(result));
    result.erase(std::unique(result.begin(), result.end()), result.end());
    return result;
}

// Filters a set of cuts to keep only the irredundant ones. A cut is redundant if it is a superset of another cut in the set.
void filter_irredundant_cuts(CutSet &cuts)
{
    if (cuts.size() <= 1)
        return;

    CutSet irredundant_cuts;
    for (const auto &candidate_cut : cuts)
    {
        bool is_subsumed = false;
        for (const auto &existing_cut : cuts)
        {
            if (candidate_cut == existing_cut)
                continue;
            // if candidate_cut is a superset of existing_cut, it's redundant.
            if (std::includes(candidate_cut.begin(), candidate_cut.end(), existing_cut.begin(), existing_cut.end()))
            {
                is_subsumed = true;
                break;
            }
        }
        if (!is_subsumed)
        {
            irredundant_cuts.insert(candidate_cut);
        }
    }
    cuts = irredundant_cuts;
}

// The main logic for enumerating k-feasible multi-output cuts and printing them.
// This is a C-linkage function that can be called from lsvCmd.cpp.
void Lsv_NtkPrintMoCut(Abc_Ntk_t *pNtk, int k_max, int l_min)
{
    // Data structure to store cuts for each node
    std::vector<CutSet> node_cuts(Abc_NtkObjNumMax(pNtk));

    // Enumerate k-feasible cuts for all nodes in topological order
    Abc_Obj_t *pObj;
    int i;
    Abc_NtkForEachObj(pNtk, pObj, i)
    {
        int obj_id = Abc_ObjId(pObj);
        if (Abc_ObjIsPi(pObj))
        {
            // Base Case: PI node. Its only cut is itself.
            node_cuts[obj_id].insert({obj_id});
        }
        else if (Abc_AigNodeIsAnd(pObj))
        {
            // Recursive Step: AND node.
            Abc_Obj_t *pFanin0 = Abc_ObjFanin0(pObj);
            Abc_Obj_t *pFanin1 = Abc_ObjFanin1(pObj);

            const auto &cuts0 = node_cuts[Abc_ObjId(pFanin0)];
            const auto &cuts1 = node_cuts[Abc_ObjId(pFanin1)];

            CutSet &current_cuts = node_cuts[obj_id];

            // Merge cuts from fanins
            for (const auto &cut0 : cuts0)
            {
                for (const auto &cut1 : cuts1)
                {
                    Cut new_cut = merge_cuts(cut0, cut1);
                    if (new_cut.size() <= k_max)
                    {
                        current_cuts.insert(new_cut);
                    }
                }
            }
            // Filter for irredundancy
            filter_irredundant_cuts(current_cuts);

            // Add the trivial unit cut {node itself}
            current_cuts.insert({obj_id});
        }
    }

    // Aggregate results to find multi-output cuts
    std::map<Cut, std::vector<int>> multi_output_cuts;

    Abc_NtkForEachObj(pNtk, pObj, i)
    {
        // Consider only PIs and AND nodes as potential "output nodes" for a cut.
        if (!Abc_ObjIsPi(pObj) && !Abc_AigNodeIsAnd(pObj))
        {
            continue;
        }

        int obj_id = Abc_ObjId(pObj);
        for (const auto &cut : node_cuts[obj_id])
        {
            // Trivial cuts on AND nodes don't need to be considered for sharing.
            if (cut.size() == 1 && cut[0] == obj_id && Abc_AigNodeIsAnd(pObj))
            {
                continue;
            }
            multi_output_cuts[cut].push_back(obj_id);
        }
    }

    // Filter by l_min and print in the specified format
    for (const auto &pair : multi_output_cuts)
    {
        const Cut &cut_leaves = pair.first;
        const std::vector<int> &output_nodes = pair.second;

        if (output_nodes.size() >= l_min)
        {
            // Print sorted input node IDs (cut leaves)
            for (size_t j = 0; j < cut_leaves.size(); ++j)
            {
                printf("%d%s", cut_leaves[j], (j == cut_leaves.size() - 1) ? "" : " ");
            }
            printf(" : ");

            // The map's value vector is not guaranteed to be sorted, so we sort it here.
            std::vector<int> sorted_outputs = output_nodes;
            std::sort(sorted_outputs.begin(), sorted_outputs.end());

            // Print sorted output node IDs
            for (size_t j = 0; j < sorted_outputs.size(); ++j)
            {
                printf("%d%s", sorted_outputs[j], (j == sorted_outputs.size() - 1) ? "" : " ");
            }
            printf("\n");
        }
    }
}