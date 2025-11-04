#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

typedef struct Lsv_CutInfo_t_ {
    Vec_Int_t *vLeaves;  // cut 的輸入節點
    Vec_Int_t *vOutputs; // 對應輸出節點
} Lsv_CutInfo_t;

static inline int Vec_IntCompare(Vec_Int_t *v1, Vec_Int_t *v2)
{
    if (Vec_IntSize(v1) != Vec_IntSize(v2)) return 0;
    int i, a, b;
    Vec_IntForEachEntryTwo(v1, v2, a, b, i)
        if (a != b) return 0;
    return 1;
}

// 檢查這個 cut 是否已經存在於 list 中
static int Lsv_FindExistingCut(Vec_Ptr_t *vCuts, Vec_Int_t *vLeaves)
{
    int i;
    Lsv_CutInfo_t *pInfo;
    Vec_PtrForEachEntry(Lsv_CutInfo_t *, vCuts, pInfo, i) {
        if (Vec_IntCompare(pInfo->vLeaves, vLeaves))
            return i;
    }
    return -1;
}

// 建立新的 cut
static Lsv_CutInfo_t *Lsv_CreateCut(Vec_Int_t *vLeaves)
{
    Lsv_CutInfo_t *pInfo = ABC_ALLOC(Lsv_CutInfo_t, 1);
    pInfo->vLeaves = Vec_IntDup(vLeaves);
    pInfo->vOutputs = Vec_IntAlloc(2);
    return pInfo;
}

// 列舉所有 cut
void Lsv_EnumerateKFeasibleCuts(Abc_Ntk_t *pNtk, int k, int l)
{
    Abc_Obj_t *pNode;
    int i;
    Vec_Ptr_t *vCuts = Vec_PtrAlloc(1000);

    Abc_NtkForEachNode(pNtk, pNode, i)
    {
        Abc_Obj_t *pFanin0 = Abc_ObjFanin0(pNode);
        Abc_Obj_t *pFanin1 = Abc_ObjFanin1(pNode);
        if (!pFanin0 || !pFanin1) continue;

        Vec_Int_t *vLeaves = Vec_IntAlloc(2);
        Vec_IntPush(vLeaves, Abc_ObjId(pFanin0));
        Vec_IntPush(vLeaves, Abc_ObjId(pFanin1));
        Vec_IntSort(vLeaves, 0);

        if (Vec_IntSize(vLeaves) > k)
        {
            Vec_IntFree(vLeaves);
            continue;
        }

        int idx = Lsv_FindExistingCut(vCuts, vLeaves);
        if (idx == -1)
        {
            Lsv_CutInfo_t *pNew = Lsv_CreateCut(vLeaves);
            Vec_IntPush(pNew->vOutputs, Abc_ObjId(pNode));
            Vec_PtrPush(vCuts, pNew);
        }
        else
        {
            Lsv_CutInfo_t *pExist = (Lsv_CutInfo_t *)Vec_PtrEntry(vCuts, idx);
            Vec_IntPush(pExist->vOutputs, Abc_ObjId(pNode));
        }

        Vec_IntFree(vLeaves);
    }

    // 印出結果
    int j, in_id, out_id;
    Lsv_CutInfo_t *pInfo;
    Vec_PtrForEachEntry(Lsv_CutInfo_t *, vCuts, pInfo, i)
    {
        if (Vec_IntSize(pInfo->vOutputs) < l)
            continue;

        // 印輸入
        Vec_IntForEachEntry(pInfo->vLeaves, in_id, j)
            Abc_Print(1, "%d ", in_id);

        Abc_Print(1, ": ");

        // 印輸出
        Vec_IntForEachEntry(pInfo->vOutputs, out_id, j)
            Abc_Print(1, "%d ", out_id);
        Abc_Print(1, "\n");
    }

    // 釋放記憶體
    Vec_PtrForEachEntry(Lsv_CutInfo_t *, vCuts, pInfo, i)
    {
        Vec_IntFree(pInfo->vLeaves);
        Vec_IntFree(pInfo->vOutputs);
        ABC_FREE(pInfo);
    }
    Vec_PtrFree(vCuts);
}

// command 主體
int Lsv_CommandPrintMoCut(Abc_Frame_t *pAbc, int argc, char **argv)
{
    if (argc != 3)
    {
        Abc_Print(-1, "Usage: lsv_printmocut <k> <l>\n");
        return 1;
    }

    int k = atoi(argv[1]);
    int l = atoi(argv[2]);
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);

    if (!pNtk)
    {
        Abc_Print(-1, "Error: No network is loaded.\n");
        return 1;
    }

    Abc_Print(1, "Running lsv_printmocut (k=%d, l=%d)\n", k, l);
    Lsv_EnumerateKFeasibleCuts(pNtk, k, l);
    Abc_Print(1, "Done.\n");

    return 0;
}

void Lsv_Init(Abc_Frame_t *pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
}
