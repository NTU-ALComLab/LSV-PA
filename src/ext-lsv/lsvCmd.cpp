#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "lsv_cut.hpp" // New cut data structures and utilities
#include <map>         
#include <algorithm>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t *pAbc, int argc, char **argv);

extern "C" void init(Abc_Frame_t *);
extern "C" void destroy(Abc_Frame_t *);

void init(Abc_Frame_t *pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
}

void destroy(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t *pNtk)
{
    Abc_Obj_t *pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
        Abc_Obj_t *pFanin;
        int j;
        Abc_ObjForEachFanin(pObj, pFanin, j)
        {
            printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
                   Abc_ObjName(pFanin));
        }
        if (Abc_NtkHasSop(pNtk))
        {
            printf("The SOP of this node:\n%s", (char *)pObj->pData);
        }
    }
}

int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF)
    {
        switch (c)
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if (!pNtk)
    {
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

// Check if cut1 is a subset of cut2 (for redundancy check)
bool IsSubset(const Cut_t &cut1, const Cut_t &cut2)
{
    return CutIsSubsetOf(cut1, cut2);
}

// Remove redundant cuts (keep only irredundant ones)
void RemoveRedundantCuts(CutList_t &cuts)
{
    CutList_t result;

    for (const auto &cut : cuts)
    {
        bool isRedundant = false;

        // Check if this cut is redundant (superset of existing cut)
        for (const auto &existing : result)
        {
            if (IsSubset(existing, cut))
            {
                isRedundant = true;
                break;
            }
        }

        if (!isRedundant)
        {
            // Remove existing cuts that are supersets of this cut
            result.erase(std::remove_if(result.begin(), result.end(),
                                        [&cut](const Cut_t &existing)
                                        {
                                            return IsSubset(cut, existing);
                                        }),
                         result.end());
            result.push_back(cut);
        }
    }

    cuts = result;
}

CutList_t EnumerateNodeCuts(Abc_Obj_t *pNode, const NodeCuts_t &nodeCuts, int k)
{
    CutList_t cuts;

    // For primary inputs, the only cut is the node itself
    if (Abc_ObjIsPi(pNode))
    {
        cuts.push_back({Abc_ObjId(pNode)});
        return cuts;
    }

    if (Abc_AigNodeIsAnd(pNode))
    {
        Abc_Obj_t *pFanin0 = Abc_ObjFanin0(pNode);
        Abc_Obj_t *pFanin1 = Abc_ObjFanin1(pNode);

        unsigned int fanin0Id = Abc_ObjId(pFanin0);
        unsigned int fanin1Id = Abc_ObjId(pFanin1);

        // Add the simplest cut (containing only this node itself)
        cuts.push_back({Abc_ObjId(pNode)});

        // Get cuts from fanins
        auto it0 = nodeCuts.find(fanin0Id);
        auto it1 = nodeCuts.find(fanin1Id);

        if (it0 != nodeCuts.end() && it1 != nodeCuts.end())
        {
            const CutList_t &cuts0 = it0->second;
            const CutList_t &cuts1 = it1->second;

            for (const auto &cut0 : cuts0)
            {
                for (const auto &cut1 : cuts1)
                {
                    Cut_t merged = MergeCuts(cut0, cut1, k);
                    if (!merged.empty())
                    {
                        cuts.push_back(merged);
                    }
                }
            }
        }

        RemoveRedundantCuts(cuts);
    }

    return cuts;
}

void Lsv_NtkReportMultiOutputCuts(Abc_Ntk_t* pNtk, int k, int l)
{
    // Must be an AIG network
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "Error: expected an AIG; run 'strash' first.\n");
        return;
    }

    NodeCuts_t cutsOfNode;
    Abc_Obj_t* pObj = nullptr;
    int i = 0;

    // Helper: enumerate and cache cuts for a given node
    const auto cacheCuts = [&](Abc_Obj_t* n) {
        cutsOfNode[Abc_ObjId(n)] = EnumerateNodeCuts(n, cutsOfNode, k);
    };

    // 1) PIs
    Abc_NtkForEachPi(pNtk, pObj, i) {
        cacheCuts(pObj);
    }

    // 2) Internal AND nodes
    Abc_NtkForEachNode(pNtk, pObj, i) {
        if (Abc_AigNodeIsAnd(pObj))
            cacheCuts(pObj);
    }

    // Build: cut -> list of sink node IDs using that cut (exclude trivial |cut|==1)
    std::map<Cut_t, std::vector<unsigned int>> sinksByCut;

    for (const auto& kv : cutsOfNode) {
        const unsigned int nodeId = kv.first;
        const CutList_t& nodeCutList = kv.second;

        Abc_Obj_t* n = Abc_NtkObj(pNtk, nodeId);
        if (Abc_ObjIsPi(n)) continue;  // PIs are not sinks

        for (const auto& cut : nodeCutList) {
            if (cut.size() <= 1) continue;  // ignore trivial cuts
            sinksByCut[cut].push_back(nodeId);
        }
    }

    // Output: "cut_inputs_sorted : sorted_unique_sinks"
    for (auto& kv : sinksByCut) {
        const Cut_t& cut = kv.first;
        std::vector<unsigned int>& sinks = kv.second;

        if (static_cast<int>(sinks.size()) < l) continue;

        // Dedup + sort sinks
        std::sort(sinks.begin(), sinks.end());
        sinks.erase(std::unique(sinks.begin(), sinks.end()), sinks.end());

        // Print cut inputs (Cut_t is an ordered set, already sorted)
        bool first = true;
        for (unsigned int inId : cut) {
            if (!first) printf(" ");
            printf("%u", inId);
            first = false;
        }

        // Print sinks
        printf(" :");
        for (unsigned int outId : sinks)
            printf(" %u", outId);
        printf("\n");
    }
}

int Lsv_CommandPrintMoCut(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    int c, k = 3, l = 2;

    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF)
    {
        switch (c)
        {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }

    // Parse command-line parameters for k and l
    if (argc != globalUtilOptind + 2)
    {
        Abc_Print(-1, "Incorrect argument count detected.\n");
        Abc_Print(-1, "Two integer parameters <k> and <l> are required.\n");
        goto usage;
    }

    k = atoi(argv[globalUtilOptind]);
    l = atoi(argv[globalUtilOptind + 1]);

    // Validate parameter ranges
    if (k < 3 || k > 6 || l < 1 || l > 4)
    {
        Abc_Print(-1, "Parameter out of range.\n");
        Abc_Print(-1, "  - k must be between 3 and 6.\n");
        Abc_Print(-1, "  - l must be between 1 and 4.\n");
        return 1;
    }

    // Check if network exists
    if (!pNtk)
    {
        Abc_Print(-1, "Error: no active network loaded.\n");
        return 1;
    }

    // Run the main functionality
    Lsv_NtkReportMultiOutputCuts(pNtk, k, l);
    return 0;

// Print help message
usage:
    Abc_Print(-2, "Command usage:\n");
    Abc_Print(-2, "  lsv_printmocut <k> <l>\n\n");
    Abc_Print(-2, "Description:\n");
    Abc_Print(-2, "  Enumerates k-l multi-output cuts in the current AIG network.\n\n");
    Abc_Print(-2, "Arguments:\n");
    Abc_Print(-2, "  <k> : limit of cut size (valid range: 3–6)\n");
    Abc_Print(-2, "  <l> : minimum number of shared outputs (valid range: 1–4)\n");
    return 1;
}