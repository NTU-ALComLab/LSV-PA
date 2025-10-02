#include "abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"

typedef struct Cut_
{
    int size;
    int nodes[6]; // Max k=6
} Cut;

typedef struct CutList_
{
    Cut *cuts;
    int nCuts;
    int maxCuts;
} CutList;

// Function to compare two cuts for equality
int CutEquals(Cut *a, Cut *b)
{
    if (a->size != b->size)
        return 0;
    for (int i = 0; i < a->size; i++)
    {
        if (a->nodes[i] != b->nodes[i])
            return 0;
    }
    return 1;
}

// Function to check if cut a is subset of cut b
int IsSubset(Cut *a, Cut *b)
{
    int i = 0, j = 0;
    while (i < a->size && j < b->size)
    {
        if (a->nodes[i] == b->nodes[j])
        {
            i++;
            j++;
        }
        else if (a->nodes[i] > b->nodes[j])
        {
            j++;
        }
        else
        {
            return 0;
        }
    }
    return (i == a->size);
}

// Function to add a cut to a list if not redundant
void AddCut(CutList *list, Cut *newCut)
{
    // Check if newCut is redundant
    for (int i = 0; i < list->nCuts; i++)
    {
        if (IsSubset(&list->cuts[i], newCut))
        {
            return; // newCut is redundant
        }
    }
    // Remove cuts that are redundant to newCut
    int i = 0;
    while (i < list->nCuts)
    {
        if (IsSubset(newCut, &list->cuts[i]))
        {
            // Remove cut i
            list->nCuts--;
            list->cuts[i] = list->cuts[list->nCuts];
        }
        else
        {
            i++;
        }
    }
    // Add newCut if space available
    if (list->nCuts < list->maxCuts)
    {
        list->cuts[list->nCuts] = *newCut;
        list->nCuts++;
    }
}

// Function to merge two cut lists
void MergeCutLists(CutList *result, CutList *list1, CutList *list2, int k)
{
    result->nCuts = 0;
    for (int i = 0; i < list1->nCuts; i++)
    {
        for (int j = 0; j < list2->nCuts; j++)
        {
            Cut newCut;
            newCut.size = 0;
            int idx1 = 0, idx2 = 0;
            while (idx1 < list1->cuts[i].size && idx2 < list2->cuts[j].size)
            {
                if (list1->cuts[i].nodes[idx1] < list2->cuts[j].nodes[idx2])
                {
                    newCut.nodes[newCut.size++] = list1->cuts[i].nodes[idx1];
                    idx1++;
                }
                else if (list1->cuts[i].nodes[idx1] > list2->cuts[j].nodes[idx2])
                {
                    newCut.nodes[newCut.size++] = list2->cuts[j].nodes[idx2];
                    idx2++;
                }
                else
                {
                    newCut.nodes[newCut.size++] = list1->cuts[i].nodes[idx1];
                    idx1++;
                    idx2++;
                }
                if (newCut.size > k)
                    break;
            }
            while (idx1 < list1->cuts[i].size && newCut.size <= k)
            {
                newCut.nodes[newCut.size++] = list1->cuts[i].nodes[idx1];
                idx1++;
            }
            while (idx2 < list2->cuts[j].size && newCut.size <= k)
            {
                newCut.nodes[newCut.size++] = list2->cuts[j].nodes[idx2];
                idx2++;
            }
            if (newCut.size <= k)
            {
                AddCut(result, &newCut);
            }
        }
    }
}

// Function to enumerate cuts for all nodes
void EnumerateCuts(Aig_Man_t *pAig, int k, CutList *nodeCuts)
{
    Aig_Obj_t *pObj;
    int i;
    // Initialize cuts for each node
    Aig_ManForEachObj(pAig, pObj, i)
    {
        nodeCuts[i].nCuts = 0;
        nodeCuts[i].maxCuts = 100; // Reasonable limit
        nodeCuts[i].cuts = ABC_CALLOC(Cut, nodeCuts[i].maxCuts);
    }
    // Process nodes in topological order
    Aig_ManForEachObj(pAig, pObj, i)
    {
        if (Aig_ObjIsConst1(pObj))
        {
            // Constant node: cut is empty?
            Cut cut;
            cut.size = 0;
            AddCut(&nodeCuts[i], &cut);
        }
        else if (Aig_ObjIsPi(pObj))
        {
            // Primary input: cut contains itself
            Cut cut;
            cut.size = 1;
            cut.nodes[0] = Aig_ObjId(pObj);
            AddCut(&nodeCuts[i], &cut);
        }
        else if (Aig_ObjIsAnd(pObj))
        {
            // AND node: merge cuts from fanins
            Aig_Obj_t *pFanin0 = Aig_ObjFanin0(pObj);
            Aig_Obj_t *pFanin1 = Aig_ObjFanin1(pObj);
            int id0 = Aig_ObjId(pFanin0);
            int id1 = Aig_ObjId(pFanin1);
            CutList mergedList;
            mergedList.nCuts = 0;
            mergedList.maxCuts = 100;
            mergedList.cuts = ABC_CALLOC(Cut, mergedList.maxCuts);
            MergeCutLists(&mergedList, &nodeCuts[id0], &nodeCuts[id1], k);
            // Add merged cuts to current node
            for (int j = 0; j < mergedList.nCuts; j++)
            {
                AddCut(&nodeCuts[i], &mergedList.cuts[j]);
            }
            ABC_FREE(mergedList.cuts);
        }
    }
}

// Main command function
int Lsv_CommandPrintMocut(Abc_Frame_t *pAbc, int argc, char **argv)
{
    if (argc != 3)
    {
        Abc_Print(-1, "Usage: lsv_printmocut <k> <l>\n");
        return 1;
    }
    int k = atoi(argv[1]);
    int l = atoi(argv[2]);
    if (k < 3 || k > 6 || l < 1 || l > 4)
    {
        Abc_Print(-1, "k must be between 3 and 6, l between 1 and 4\n");
        return 1;
    }

    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk)
    {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk))
    {
        Abc_Print(-1, "Network is not in AIG form. Please run 'strash' first.\n");
        return 1;
    }

    Aig_Man_t *pAig = Abc_NtkToDar(pNtk, 0, 0);
    if (!pAig)
    {
        Abc_Print(-1, "Conversion to AIG failed.\n");
        return 1;
    }

    int nNodes = Aig_ManObjNumMax(pAig);
    CutList *nodeCuts = ABC_CALLOC(CutList, nNodes);

    EnumerateCuts(pAig, k, nodeCuts);

    // Create a map from cut to list of nodes that have it
    Vec_Ptr_t *cutMap = Vec_PtrAlloc(100);
    Vec_Int_t *cutHash = Vec_IntAlloc(100);
    for (int i = 0; i < nNodes; i++)
    {
        Aig_Obj_t *pObj = Aig_ManObj(pAig, i);
        if (!Aig_ObjIsAnd(pObj) && !Aig_ObjIsPi(pObj))
            continue;
        for (int j = 0; j < nodeCuts[i].nCuts; j++)
        {
            Cut *cut = &nodeCuts[i].cuts[j];
            // Create a unique key for the cut
            int key = 0;
            for (int m = 0; m < cut->size; m++)
            {
                key = key * 131 + cut->nodes[m];
            }
            // Find or create entry in cutMap
            int found = 0;
            for (int n = 0; n < Vec_PtrSize(cutMap); n++)
            {
                Cut *existingCut = Vec_PtrEntry(cutMap, n);
                if (CutEquals(cut, existingCut))
                {
                    Vec_IntAddToEntry(cutHash, n, i);
                    found = 1;
                    break;
                }
            }
            if (!found)
            {
                Cut *newCut = ABC_ALLOC(Cut, 1);
                *newCut = *cut;
                Vec_PtrPush(cutMap, newCut);
                Vec_IntPush(cutHash, i);
            }
        }
    }

    // Print cuts with at least l outputs
    for (int i = 0; i < Vec_PtrSize(cutMap); i++)
    {
        Cut *cut = Vec_PtrEntry(cutMap, i);
        int count = 0;
        for (int j = 0; j < Vec_IntSize(cutHash); j++)
        {
            if (Vec_IntEntry(cutHash, j) == i)
                count++;
        }
        if (count >= l)
        {
            // Print cut inputs
            for (int m = 0; m < cut->size; m++)
            {
                Abc_Print(1, "%d", cut->nodes[m]);
                if (m < cut->size - 1)
                    Abc_Print(1, " ");
            }
            Abc_Print(1, " : ");
            // Print output nodes
            int first = 1;
            for (int j = 0; j < Vec_IntSize(cutHash); j++)
            {
                if (Vec_IntEntry(cutHash, j) == i)
                {
                    if (!first)
                        Abc_Print(1, " ");
                    Abc_Print(1, "%d", j);
                    first = 0;
                }
            }
            Abc_Print(1, "\n");
        }
    }

    // Free memory
    for (int i = 0; i < nNodes; i++)
    {
        if (nodeCuts[i].cuts)
            ABC_FREE(nodeCuts[i].cuts);
    }
    ABC_FREE(nodeCuts);
    Aig_ManStop(pAig);
    return 0;
}

// Command registration
void Lsv_Init(Abc_Frame_t *pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMocut, 0);
}
