// lsvMoc.c

#include "misc/st/st.h"
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"

// 函數前向宣告
void Lsv_NtkPrintMocut(Abc_Ntk_t *pNtk, int k, int l);
int Lsv_CommandPrintMocut(Abc_Frame_t *pAbc, int argc, char **argv);

// 輔助函數
static Vec_Int_t *Lsv_MergeCuts(Vec_Int_t *vCut0, Vec_Int_t *vCut1, int k)
{
    Vec_Int_t *vNew = Vec_IntAlloc(Vec_IntSize(vCut0) + Vec_IntSize(vCut1));
    int i = 0, j = 0;
    while (i < Vec_IntSize(vCut0) && j < Vec_IntSize(vCut1))
    {
        if (Vec_IntEntry(vCut0, i) < Vec_IntEntry(vCut1, j))
            Vec_IntPush(vNew, Vec_IntEntry(vCut0, i++));
        else if (Vec_IntEntry(vCut0, i) > Vec_IntEntry(vCut1, j))
            Vec_IntPush(vNew, Vec_IntEntry(vCut1, j++));
        else
        {
            Vec_IntPush(vNew, Vec_IntEntry(vCut0, i++));
            j++;
        }
        if (Vec_IntSize(vNew) > k)
        {
            Vec_IntFree(vNew);
            return NULL;
        }
    }
    for (; i < Vec_IntSize(vCut0); i++)
        Vec_IntPush(vNew, Vec_IntEntry(vCut0, i));
    for (; j < Vec_IntSize(vCut1); j++)
        Vec_IntPush(vNew, Vec_IntEntry(vCut1, j));
    if (Vec_IntSize(vNew) > k)
    {
        Vec_IntFree(vNew);
        return NULL;
    }
    return vNew;
}

// 核心演算法
void Lsv_NtkPrintMocut(Abc_Ntk_t *pNtk, int k, int l)
{
    Vec_Ptr_t **vCutSets = (Vec_Ptr_t **)ABC_CALLOC(Vec_Ptr_t *, Abc_NtkObjNumMax(pNtk));
    Abc_Obj_t *pObj;
    int i;

    // 步驟 1: 初始化常數節點
    Abc_Obj_t *pConst1 = Abc_AigConst1(pNtk);
    if (pConst1 != NULL)
    {
        vCutSets[pConst1->Id] = Vec_PtrAlloc(1);
    }

    // 步驟 2: 為所有主要輸入 (PI) 建立 Trivial Cut
    Abc_NtkForEachPi(pNtk, pObj, i)
    {
        vCutSets[pObj->Id] = Vec_PtrAlloc(1);
        Vec_Int_t *vCut = Vec_IntAlloc(1);
        Vec_IntPush(vCut, pObj->Id);
        Vec_PtrPush(vCutSets[pObj->Id], vCut);
    }

    // 步驟 3: 為所有閂鎖 (Latch) 建立 Trivial Cut，將它們視為 PI
    Abc_NtkForEachLatch(pNtk, pObj, i)
    {
        vCutSets[pObj->Id] = Vec_PtrAlloc(1);
        Vec_Int_t *vCut = Vec_IntAlloc(1);
        Vec_IntPush(vCut, pObj->Id);
        Vec_PtrPush(vCutSets[pObj->Id], vCut);
    }

    // 步驟 4: 按照拓撲順序處理所有內部 AND 節點
    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        vCutSets[pObj->Id] = Vec_PtrAlloc(16);
        Vec_Int_t *vTrivialCut = Vec_IntAlloc(1);
        Vec_IntPush(vTrivialCut, pObj->Id);
        Vec_PtrPush(vCutSets[pObj->Id], vTrivialCut);

        Abc_Obj_t *pFanin0 = Abc_ObjFanin0(pObj);
        Abc_Obj_t *pFanin1 = Abc_ObjFanin1(pObj);
        Vec_Ptr_t *vCuts0 = vCutSets[pFanin0->Id];
        Vec_Ptr_t *vCuts1 = vCutSets[pFanin1->Id];

        Vec_Int_t *vCut0, *vCut1;
        int j, m;
        Vec_PtrForEachEntry(Vec_Int_t *, vCuts0, vCut0, j)
        {
            Vec_PtrForEachEntry(Vec_Int_t *, vCuts1, vCut1, m)
            {
                Vec_Int_t *vNewCut = Lsv_MergeCuts(vCut0, vCut1, k);
                if (vNewCut != NULL)
                    Vec_PtrPush(vCutSets[pObj->Id], vNewCut);
            }
        }
    }

    // Phase 2 & 3: 收集、過濾與輸出
    st__table *stCutMap = st__init_table(strcasecmp, st__strhash);
    char pBuffer[1000];
    Abc_NtkForEachNode(pNtk, pObj, i)
    { // 只遍歷 Node
        Vec_Ptr_t *vCuts = vCutSets[pObj->Id];
        Vec_Int_t *vCut;
        int j;
        Vec_PtrForEachEntry(Vec_Int_t *, vCuts, vCut, j)
        {
            char *pTemp = pBuffer;
            int NodeId, m;
            Vec_IntForEachEntry(vCut, NodeId, m) pTemp += sprintf(pTemp, "%d ", NodeId);
            *pTemp = 0;
            Vec_Int_t *vOutNodes;
            if (!st__lookup(stCutMap, pBuffer, (char **)&vOutNodes))
            {
                vOutNodes = Vec_IntAlloc(4);
                char *pKey = Abc_UtilStrsav(pBuffer);
                st__insert(stCutMap, pKey, (char *)vOutNodes);
            }
            Vec_IntPush(vOutNodes, pObj->Id);
        }
    }

    st__generator *gen;
    const char *pKey;
    char *pValue;
    st__foreach_item(stCutMap, gen, &pKey, &pValue)
    {
        Vec_Int_t *vOutNodes = (Vec_Int_t *)pValue;
        if (Vec_IntSize(vOutNodes) >= l)
        {
            Vec_IntSort(vOutNodes, 0);
            printf("%s :", pKey);
            int NodeId, m;
            Vec_IntForEachEntry(vOutNodes, NodeId, m) printf(" %d", NodeId);
            printf("\n");
        }
    }
    st__free_gen(gen);

    // Phase 4: 記憶體釋放
    st__foreach_item(stCutMap, gen, &pKey, &pValue)
    {
        free((char *)pKey);
        Vec_IntFree((Vec_Int_t *)pValue);
    }
    st__free_table(stCutMap);

    Abc_NtkForEachObj(pNtk, pObj, i)
    {
        Vec_Ptr_t *vCuts = vCutSets[pObj->Id];
        if (vCuts == NULL)
            continue;
        Vec_Int_t *vCut;
        int j;
        Vec_PtrForEachEntry(Vec_Int_t *, vCuts, vCut, j) Vec_IntFree(vCut);
        Vec_PtrFree(vCuts);
    }
    ABC_FREE(vCutSets);
}

// 指令進入點函數
int Lsv_CommandPrintMocut(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    int k, l;
    if (argc != 3)
        goto usage;
    if (!pNtk)
    {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk))
    {
        Abc_Print(-1, "Network is not an AIG. Please run 'strash' first.\n");
        return 1;
    }
    k = atoi(argv[1]);
    l = atoi(argv[2]);
    if (k < 3 || k > 6 || l < 1 || l > 4)
    {
        Abc_Print(-1, "Error: Invalid parameters. k must be in [3, 6] and l in [1, 4].\n");
        return 1;
    }
    Lsv_NtkPrintMocut(pNtk, k, l);
    return 0;
usage:
    Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
    Abc_Print(-2, "\t        enumerates k-l multi-output cuts in an AIG\n");
    Abc_Print(-2, "\t-k    : the maximum number of nodes in a cut (3 <= k <= 6)\n");
    Abc_Print(-2, "\t-l    : the minimum number of outputs sharing a cut (1 <= l <= 4)\n");
    return 1;
}
