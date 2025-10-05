#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"
#include "misc/vec/vecPtr.h"
#include "misc/st/st.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMultiOutputCut(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMultiOutputCut, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
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

void Lsv_End(Abc_Frame_t *pAbc) {}

//  Helper structures

typedef struct Cut_t_
{
    Vec_Ptr_t *vInputs;  // PI/AND nodes in the cut
} Cut_t;


//  Helper functions

/** Create a new single-node cut **/
static Cut_t *Cut_CreateSingle(Abc_Obj_t *pObj)
{
    Cut_t *pCut = (Cut_t *)ABC_ALLOC(Cut_t, 1);
    pCut->vInputs = Vec_PtrAlloc(1);
    Vec_PtrPush(pCut->vInputs, pObj);
    return pCut;
}

/** Duplicate a cut **/
static Cut_t *Cut_Dup(Cut_t *pCut)
{
    Cut_t *pNew = (Cut_t *)ABC_ALLOC(Cut_t, 1);
    pNew->vInputs = Vec_PtrDup(pCut->vInputs);
    return pNew;
}

/** Merge two cuts (union of inputs) **/
static Cut_t *Cut_Merge(Cut_t *pCut0, Cut_t *pCut1, int k)
{
    Vec_Ptr_t *v0 = pCut0->vInputs;
    Vec_Ptr_t *v1 = pCut1->vInputs;

    // create sorted unique union
    Vec_Ptr_t *vUnion = Vec_PtrAlloc(Vec_PtrSize(v0) + Vec_PtrSize(v1));
    for (int i = 0; i < Vec_PtrSize(v0); i++)
        Vec_PtrPushUnique(vUnion, Vec_PtrEntry(v0, i));
    for (int i = 0; i < Vec_PtrSize(v1); i++)
        Vec_PtrPushUnique(vUnion, Vec_PtrEntry(v1, i));

    if (Vec_PtrSize(vUnion) > k)
    {
        Vec_PtrFree(vUnion);
        return NULL;
    }

    Cut_t *pNew = (Cut_t *)ABC_ALLOC(Cut_t, 1);
    pNew->vInputs = vUnion;
    return pNew;
}

/** Recursively enumerate all cuts for a node **/
static void Lsv_EnumCuts_rec(Abc_Obj_t *pObj, int k, st__table *memo)
{
    // Already computed?
    if (st__is_member(memo, (char *)pObj))
        return;

    Vec_Ptr_t *vCuts = Vec_PtrAlloc(16);

    if (Abc_ObjIsPi(pObj))
    {
        Vec_PtrPush(vCuts, Cut_CreateSingle(pObj));
        st__insert(memo, (char *)pObj, (char *)vCuts);
        return;
    }

    Abc_Obj_t *pF0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t *pF1 = Abc_ObjFanin1(pObj);

    Lsv_EnumCuts_rec(pF0, k, memo);
    Lsv_EnumCuts_rec(pF1, k, memo);

    Vec_Ptr_t *vCuts0 = NULL;
    Vec_Ptr_t *vCuts1 = NULL;
    st__lookup(memo, (char *)pF0, (char **)&vCuts0);
    st__lookup(memo, (char *)pF1, (char **)&vCuts1);

    // Merge every pair of cuts from the two fanins
    for (int i = 0; i < Vec_PtrSize(vCuts0); i++)
    {
        for (int j = 0; j < Vec_PtrSize(vCuts1); j++)
        {
            Cut_t *pNew = Cut_Merge((Cut_t *)Vec_PtrEntry(vCuts0, i),
                                    (Cut_t *)Vec_PtrEntry(vCuts1, j), k);
            if (pNew)
                Vec_PtrPush(vCuts, pNew);
        }
    }

    // Also include the unit cut {this node}
    Vec_PtrPush(vCuts, Cut_CreateSingle(pObj));
    st__insert(memo, (char *)pObj, (char *)vCuts);
}

/** Free all cuts **/
static void Lsv_FreeCuts(st__table *memo)
{
    st__generator *gen;
    const char *key;
    Vec_Ptr_t *vCuts;
    for (gen = st__init_gen(memo); st__gen(gen, &key, (char **)&vCuts); )
    {
        for (int i = 0; i < Vec_PtrSize(vCuts); i++)
        {
            Cut_t *pCut = (Cut_t *)Vec_PtrEntry(vCuts, i);
            Vec_PtrFree(pCut->vInputs);
            ABC_FREE(pCut);
        }
        Vec_PtrFree(vCuts);
    }
    st__gen_free(gen);
}

/** Convert cut to string key (sorted ascending IDs) **/
static char *Cut_ToKey(Cut_t *pCut)
{
    static char buffer[256];
    buffer[0] = '\0';
    int n = Vec_PtrSize(pCut->vInputs);
    int ids[64];
    for (int i = 0; i < n; i++)
        ids[i] = Abc_ObjId((Abc_Obj_t *)Vec_PtrEntry(pCut->vInputs, i));
    // simple bubble sort
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (ids[j] < ids[i])
            {
                int t = ids[i];
                ids[i] = ids[j];
                ids[j] = t;
            }
    for (int i = 0; i < n; i++)
    {
        char tmp[16];
        sprintf(tmp, "%d ", ids[i]);
        strcat(buffer, tmp);
    }
    return buffer;
}

/** Print cut with inputs:outputs **/
static void PrintCutLine(Vec_Ptr_t *vInputs, Vec_Ptr_t *vOutputs)
{
    int i;
    for (i = 0; i < Vec_PtrSize(vInputs); i++)
        Abc_Print(1, "%d ", Abc_ObjId((Abc_Obj_t *)Vec_PtrEntry(vInputs, i)));
    Abc_Print(1, ": ");
    for (i = 0; i < Vec_PtrSize(vOutputs); i++)
        Abc_Print(1, "%d ", Abc_ObjId((Abc_Obj_t *)Vec_PtrEntry(vOutputs, i)));
    Abc_Print(1, "\n");
}


//  Main command

static int Lsv_CommandPrintMultiOutputCut(Abc_Frame_t *pAbc, int argc, char **argv)
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
        Abc_Print(-1, "Error: no network loaded.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk))
    {
        Abc_Print(-1, "Error: please run \"strash\" first.\n");
        return 1;
    }

    // Step 1: Enumerate cuts recursively for each node
    st__table *memo = st__init_table(st__ptrcmp, st__ptrhash);
    Abc_Obj_t *pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i)
        Lsv_EnumCuts_rec(pObj, k, memo);

    // Step 2: Map cut-key → vector of output nodes
    st__table *cutMap = st__init_table(strcmp, st__strhash);

    Abc_NtkForEachPo(pNtk, pObj, i)
    {
        Abc_Obj_t *pFanin = Abc_ObjFanin0(pObj);
        Vec_Ptr_t *vCuts = NULL;
        if (!st__lookup(memo, (char *)pFanin, (char **)&vCuts))
            continue;
        for (int j = 0; j < Vec_PtrSize(vCuts); j++)
        {
            Cut_t *pCut = (Cut_t *)Vec_PtrEntry(vCuts, j);
            char *key = Cut_ToKey(pCut);
            Vec_Ptr_t *vOuts;
            if (!st__lookup(cutMap, key, (char **)&vOuts))
            {
                vOuts = Vec_PtrAlloc(4);
                st__insert(cutMap, Extra_UtilStrsav(key), (char *)vOuts);
            }
            Vec_PtrPushUnique(vOuts, pFanin);
        }
    }

    // Step 3: Print cuts shared by >= l outputs
    st__generator *gen;
    const char *key;
    Vec_Ptr_t *vOuts;
    for (gen = st__init_gen(cutMap); st__gen(gen, &key, (char **)&vOuts); )
    {
        if (Vec_PtrSize(vOuts) >= l)
        {
            Vec_Ptr_t *vInputs = Vec_PtrAlloc(4);
            char *keyCopy = Extra_UtilStrsav(key);  // strtok modifies string
            char *tok = strtok(keyCopy, " ");
            while (tok)
            {
                int id = atoi(tok);
                Abc_Obj_t *pIn = Abc_NtkObj(pNtk, id);
                Vec_PtrPush(vInputs, pIn);
                tok = strtok(NULL, " ");
            }
            PrintCutLine(vInputs, vOuts);
            Vec_PtrFree(vInputs);
            ABC_FREE(keyCopy);
        }
    }
    st__gen_free(gen);

    // Step 4: Cleanup
    Lsv_FreeCuts(memo);
    st__free_table(memo);
    st__free_table(cutMap);

    return 0;
}
