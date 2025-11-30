#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"
#include "misc/vec/vecPtr.h"
#include "misc/st/st.h"
extern "C" {
#include "bdd/cudd/cudd.h"
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMultiOutputCut(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandUnateBdd( Abc_Frame_t* pAbc, int argc, char** argv );
static int Lsv_CommandUnateSat( Abc_Frame_t* pAbc, int argc, char** argv );

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMultiOutputCut, 0);
  Cmd_CommandAdd( pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0 );
  Cmd_CommandAdd( pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0 );
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

/** Check if cut A is a subset of cut B **/
static int Cut_IsSubset(Cut_t *pA, Cut_t *pB)
{
    Vec_Ptr_t *vA = pA->vInputs;
    Vec_Ptr_t *vB = pB->vInputs;

    for (int i = 0; i < Vec_PtrSize(vA); i++)
    {
        Abc_Obj_t *pObjA = (Abc_Obj_t *)Vec_PtrEntry(vA, i);
        int found = 0;
        for (int j = 0; j < Vec_PtrSize(vB); j++)
        {
            if (pObjA == Vec_PtrEntry(vB, j))
            {
                found = 1;
                break;
            }
        }
        if (!found)
            return 0;
    }
    return 1;
}

/** Remove redundant cuts (supersets) from vCuts **/
static void Cuts_RemoveRedundant(Vec_Ptr_t *vCuts)
{
    int i, j;
    for (i = 0; i < Vec_PtrSize(vCuts); i++)
    {
        Cut_t *pCi = (Cut_t *)Vec_PtrEntry(vCuts, i);
        if (!pCi) continue;

        for (j = 0; j < Vec_PtrSize(vCuts); j++)
        {
            if (i == j) continue;
            Cut_t *pCj = (Cut_t *)Vec_PtrEntry(vCuts, j);
            if (!pCj) continue;

            // If Ci is a superset of Cj, remove Ci
            if (Cut_IsSubset(pCj, pCi))
            {
                Vec_PtrWriteEntry(vCuts, i, NULL);
                Vec_PtrFree(pCi->vInputs);
                ABC_FREE(pCi);
                break;
            }
        }
    }

    // Compact the vector (remove NULLs)
    Vec_Ptr_t *vNew = Vec_PtrAlloc(Vec_PtrSize(vCuts));
    for (i = 0; i < Vec_PtrSize(vCuts); i++)
    {
        Cut_t *pC = (Cut_t *)Vec_PtrEntry(vCuts, i);
        if (pC)
            Vec_PtrPush(vNew, pC);
    }
    Vec_PtrClear(vCuts);
    Vec_PtrAppend(vCuts, vNew);
    Vec_PtrFree(vNew);
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
    Cuts_RemoveRedundant(vCuts);
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
    st__free_gen(gen);
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
    if (argc == 2 && strcmp(argv[1], "-h") == 0)
    {
        Abc_Print(-2, "usage: lsv_printmocut [-h] [<k>] [<l>]\n");
        Abc_Print(-2, "\t        enumerate k-l multi-output cuts in an AIG\n");
        Abc_Print(-2, "\t-h    : print the command usage\n");
        return 1;
    }
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
    st__free_gen(gen);

    // Step 4: Cleanup
    Lsv_FreeCuts(memo);
    st__free_table(memo);
    st__free_table(cutMap);

    return 0;
}


////////////////////pa2///////////////////////

static void Lsv_NtkUnateBdd( Abc_Ntk_t* pNtk, int k, int i );

static int Lsv_CommandUnateBdd( Abc_Frame_t* pAbc, int argc, char** argv )
{
    Abc_Ntk_t* pNtk;
    int k, i;

    if ( argc != 3 ) {
        Abc_Print( -1, "usage: lsv_unate_bdd <k> <i>\n" );
        return 1;
    }

    k = atoi( argv[1] );
    i = atoi( argv[2] );

    pNtk = Abc_FrameReadNtk( pAbc );
    if ( pNtk == NULL ) {
        Abc_Print( -1, "Error: empty network.\n" );
        return 1;
    }
    if ( k < 0 || k >= Abc_NtkCoNum( pNtk ) ) {
        Abc_Print( -1, "Error: k (= %d) is out of range [0, %d).\n", k, Abc_NtkCoNum(pNtk) );
        return 1;
    }
    if ( i < 0 || i >= Abc_NtkCiNum( pNtk ) ) {
        Abc_Print( -1, "Error: i (= %d) is out of range [0, %d).\n", i, Abc_NtkCiNum(pNtk) );
        return 1;
    }

    Lsv_NtkUnateBdd( pNtk, k, i );
    return 0;
}

static char* Lsv_BddPickPattern( DdManager* dd, DdNode* bFunc,
                                 int nPis, int skipVar ); // 下面實作

static void Lsv_NtkUnateBdd( Abc_Ntk_t* pNtk, int k, int i )
{
    // Make sure network is AIG before building global BDDs
    if ( !Abc_NtkIsStrash(pNtk) ) {
        pNtk = Abc_NtkStrash( pNtk, 1, 1, 0 );
    }
    Abc_Obj_t* pCo;
    DdManager* dd = NULL;
    DdNode *f, *var, *f0, *f1;
    DdNode *badPos, *badNeg;
    DdNode* bZero = NULL;
    int nPis = Abc_NtkCiNum( pNtk );

    // 取得第 k 個 CO（PO）
    pCo = Abc_NtkCo( pNtk, k );

    // 建立 global BDD
    dd = (DdManager*) Abc_NtkBuildGlobalBdds( pNtk, 10000000, 1, 1, 0, 0 );
    if ( dd == NULL ) {
        Abc_Print( -1, "Error: cannot build global BDDs.\n" );
        return;
    }

    f = (DdNode*)Abc_ObjGlobalBdd( pCo ); // 不要 deref f，manager 會處理
    if ( f == NULL ) {
        Abc_Print( -1, "Error: CO %d has no global BDD.\n", k );
        Abc_NtkFreeGlobalBdds( pNtk, 1 );
        return;
    }

    // 取得對應的 BDD 變數 x_i
    var = Cudd_bddIthVar( dd, i );
    Cudd_Ref( var );

    // f1 = f with x_i = 1
    f1 = Cudd_Cofactor( dd, f, var );
    Cudd_Ref( f1 );

    // f0 = f with x_i = 0
    f0 = Cudd_Cofactor( dd, f, Cudd_Not(var) );
    Cudd_Ref( f0 );

    Cudd_RecursiveDeref( dd, var );

    bZero = Cudd_ReadLogicZero( dd );

    // 先判斷 independent
    if ( f0 == f1 ) {
        Abc_Print( 1, "independent\n" );
        Cudd_RecursiveDeref( dd, f0 );
        Cudd_RecursiveDeref( dd, f1 );
        Abc_NtkFreeGlobalBdds( pNtk, 1 );
        return;
    }

    // badPos = f0 & !f1  (找 f(0,a)=1 且 f(1,a)=0 的 assignment)
    badPos = Cudd_bddAnd( dd, f0, Cudd_Not(f1) );
    Cudd_Ref( badPos );

    // badNeg = !f0 & f1  (找 f(0,a)=0 且 f(1,a)=1 的 assignment)
    badNeg = Cudd_bddAnd( dd, Cudd_Not(f0), f1 );
    Cudd_Ref( badNeg );

    if ( badPos == bZero && badNeg == bZero ) {
        // 理論上不會走到這裡（f0!=f1又沒有 violation），當作 independent
        Abc_Print( 1, "independent\n" );
    }
    else if ( badPos == bZero && badNeg != bZero ) {
        // 沒有 (1,0) counterexample ⇒ positive unate
        Abc_Print( 1, "positive unate\n" );
    }
    else if ( badPos != bZero && badNeg == bZero ) {
        // 沒有 (0,1) counterexample ⇒ negative unate
        Abc_Print( 1, "negative unate\n" );
    }
    else {
        // 兩種 violation 都有 ⇒ binate，需要輸出兩個 pattern
        char* pat1;
        char* pat2;
        Abc_Print( 1, "binate\n" );

        pat1 = Lsv_BddPickPattern( dd, badNeg, nPis, i ); // f(0,a)=0, f(1,a)=1
        pat2 = Lsv_BddPickPattern( dd, badPos, nPis, i ); // f(0,b)=1, f(1,b)=0

        if ( pat1 ) {
            Abc_Print( 1, "%s\n", pat1 );
            ABC_FREE( pat1 );
        }
        if ( pat2 ) {
            Abc_Print( 1, "%s\n", pat2 );
            ABC_FREE( pat2 );
        }
    }

    Cudd_RecursiveDeref( dd, badPos );
    Cudd_RecursiveDeref( dd, badNeg );
    Cudd_RecursiveDeref( dd, f0 );
    Cudd_RecursiveDeref( dd, f1 );
    Abc_NtkFreeGlobalBdds( pNtk, 1 );
}

static char* Lsv_BddPickPattern( DdManager* dd, DdNode* bFunc,
                                 int nPis, int skipVar )
{
    int nVars = Cudd_ReadSize( dd );
    int v;
    // Cudd_bddPickOneCube 會回傳一個長度 = #vars 的陣列
    // 元素為 0 / 1 / 2 (don't care)
    char* cube = (char*)ABC_ALLOC( char, nVars );
    char* pattern;

    if ( bFunc == Cudd_ReadLogicZero(dd) ) {
        ABC_FREE( cube );
        return NULL;
    }

    if ( !Cudd_bddPickOneCube( dd, bFunc, cube ) ) {
        ABC_FREE( cube );
        return NULL;
    }

    pattern = (char*)ABC_ALLOC( char, nPis + 1 );
    for ( v = 0; v < nPis; ++v ) {
        if ( v == skipVar ) {
            pattern[v] = '-';
        }
        else {
            char c = cube[v];
            if ( c == 0 )      pattern[v] = '0';
            else if ( c == 1 ) pattern[v] = '1';
            else               pattern[v] = '0'; // don't-care 任選 0 或 1
        }
    }
    pattern[nPis] = '\0';

    ABC_FREE( cube );
    return pattern;
}

extern "C" {
#include "base/abc/abc.h"
#include "sat/cnf/cnf.h"

// 從 Abc_Ntk 轉成 AIG
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t* pNtk, int fExors, int fRegisters );
}

static int  Lsv_CommandUnateSat( Abc_Frame_t* pAbc, int argc, char** argv );
static void Lsv_NtkUnateSat( Abc_Ntk_t* pNtk, int k, int i );
static char* Lsv_SatPatternFromModel( sat_solver* pSat,
                                      int* piVarA, int nPis, int iSkip );

static int Lsv_CommandUnateSat( Abc_Frame_t* pAbc, int argc, char** argv )
{
    Abc_Ntk_t* pNtk;
    int k, i;

    if ( argc != 3 ) {
        Abc_Print( -1, "usage: lsv_unate_sat <k> <i>\n" );
        return 1;
    }

    k = atoi( argv[1] );
    i = atoi( argv[2] );

    pNtk = Abc_FrameReadNtk( pAbc );
    if ( !pNtk ) {
        Abc_Print( -1, "Error: empty network.\n" );
        return 1;
    }
    if ( k < 0 || k >= Abc_NtkCoNum(pNtk) ) {
        Abc_Print( -1, "Error: k out of range.\n" );
        return 1;
    }
    if ( i < 0 || i >= Abc_NtkPiNum(pNtk) ) {
        Abc_Print( -1, "Error: i out of range.\n" );
        return 1;
    }

    Lsv_NtkUnateSat( pNtk, k, i );
    return 0;
}

#include "sat/bsat/satSolver.h"

// 建一個 id->PI index 的表，方便 mapping
static void Lsv_BuildPiId2Index( Abc_Ntk_t* pNtk, Vec_Int_t* vId2Pi )
{
    Abc_Obj_t* pObj;
    int i;
    Vec_IntFill( vId2Pi, Abc_NtkObjNumMax(pNtk) + 1, -1 );
    Abc_NtkForEachPi( pNtk, pObj, i ) {
        Vec_IntWriteEntry( vId2Pi, pObj->Id, i );
    }
}

static char * Lsv_SatPatternFromModel( sat_solver * pSat, int * piVarA, int nPis, int iSkip )
{
    // Helper: read var values from solver model and produce pattern string.
    // sat_solver_var_value returns 0/1 (or -1 for unknown) in many ABC versions.
    char * pattern = (char*) ABC_ALLOC( char, nPis + 1 );
    for ( int i = 0; i < nPis; ++i ) {
        if ( i == iSkip ) { pattern[i] = '-'; continue; }
        if ( piVarA[i] < 0 ) { pattern[i] = '0'; continue; } // PI not in cone
        int val = sat_solver_var_value( pSat, piVarA[i] );
        if ( val == 0 ) pattern[i] = '0';
        else if ( val == 1 ) pattern[i] = '1';
        else pattern[i] = '0';
    }
    pattern[nPis] = '\0';
    return pattern;
}

static void Lsv_NtkUnateSat( Abc_Ntk_t * pNtk, int k, int iPi )
{
    if ( pNtk == NULL ) {
        Abc_Print( -1, "Error: empty network\n" );
        return;
    }
    if ( k < 0 || k >= Abc_NtkCoNum(pNtk) ) {
        Abc_Print( -1, "Error: CO index out of range\n" );
        return;
    }
    if ( iPi < 0 || iPi >= Abc_NtkCiNum(pNtk) ) {
        Abc_Print( -1, "Error: CI index out of range\n" );
        return;
    }

    // --- build cone correctly (use fanin0 of the CO node) ---
    Abc_Obj_t * pCo = Abc_NtkCo( pNtk, k );
    if ( pCo == NULL ) {
        Abc_Print( -1, "Error: cannot find CO %d\n", k );
        return;
    }
    Abc_Obj_t * pRoot = Abc_ObjFanin0( pCo ); // IMPORTANT: use fanin0
    if ( pRoot == NULL || !Abc_ObjIsNode(pRoot) && !Abc_ObjIsCi(pRoot) ) {
        Abc_Print( -1, "Error: CO %d has no valid fanin root\n", k );
        return;
    }

    Abc_Ntk_t * pCone = Abc_NtkCreateCone( pNtk, pRoot, Abc_ObjName(pCo), 0 );
    if ( pCone == NULL ) {
        Abc_Print( -1, "Error: Abc_NtkCreateCone failed\n" );
        return;
    }

    // Ensure cone is strashed (AIG) before CNF derive
    Abc_Ntk_t * pConeAig = pCone;
    if ( !Abc_NtkIsStrash( pCone ) ) {
        pConeAig = Abc_NtkStrash( pCone, 1, 1, 0 ); // (fAllNodes=1, fCleanup=1, fRecord=0)
        if ( pConeAig == NULL ) {
            Abc_Print( -1, "Error: Abc_NtkStrash on cone failed\n" );
            Abc_NtkDelete( pCone );
            return;
        }
    }

    // Convert AIG to AIG manager if necessary (Abc_NtkToDar returns Aig_Man_t*)
    Aig_Man_t * pAig = Abc_NtkToDar( pConeAig, 0, 0 );
    if ( pAig == NULL ) {
        Abc_Print( -1, "Error: Abc_NtkToDar failed\n" );
        if ( pConeAig != pCone ) Abc_NtkDelete( pConeAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // Derive CNF for A (first copy)
    Cnf_Dat_t * pCnfA = Cnf_Derive( pAig, 1 );
    if ( pCnfA == NULL ) {
        Abc_Print( -1, "Error: Cnf_Derive A failed\n" );
        Aig_ManStop( pAig );
        if ( pConeAig != pCone ) Abc_NtkDelete( pConeAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // Derive CNF for B (second copy)
    Cnf_Dat_t * pCnfB = Cnf_Derive( pAig, 1 );
    if ( pCnfB == NULL ) {
        Abc_Print( -1, "Error: Cnf_Derive B failed\n" );
        Cnf_DataFree( pCnfA );
        Aig_ManStop( pAig );
        if ( pConeAig != pCone ) Abc_NtkDelete( pConeAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // Lift CNF B variable indices by pCnfA->nVars
    Cnf_DataLift( pCnfB, pCnfA->nVars );

    // Create SAT solver and set number of variables
    sat_solver * pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pCnfA->nVars + pCnfB->nVars );

    // Write CNFs into solver
    Cnf_DataWriteIntoSolverInt( pSat, pCnfA, 1, 0 );
    Cnf_DataWriteIntoSolverInt( pSat, pCnfB, 1, 0 );

    // Map PI variables:
    // pCone's PIs correspond to some original PIs — we need mapping from original PI index to var in CA/CB.
    // We'll build piVarA[origPiIndex] / piVarB[origPiIndex] arrays. Default -1 means PI not in cone.
    int nOrigPis = Abc_NtkCiNum( pNtk );
    int * piVarA = (int*) ABC_ALLOC( int, nOrigPis );
    int * piVarB = (int*) ABC_ALLOC( int, nOrigPis );
    for ( int idx = 0; idx < nOrigPis; ++idx ) { piVarA[idx] = -1; piVarB[idx] = -1; }

    // Build mapping: iterate cone's PIs; each cone PI has pObj->pCopy set to AIG obj earlier in strash pipeline
    int j = 0;
    Abc_Obj_t * pPi;
    Abc_NtkForEachPi( pConeAig, pPi, j ) {
        // In many ABC flows, pPi->pCopy contains the corresponding AIG object id (Aig_Obj_t*), but easier:
        // find its original PI index by name or Id: assume the cone PI came from original network CI and retains Id.
        int origId = Abc_ObjOriginalId( pPi ); // if not available, try pPi->Id
        // Fallback: use pPi->Id and hope original CI Id matches; if not, user may need to customize mapping.
        int origIdx = -1;
        // Try to get original PI index by scanning original network PIs by Id
        Abc_Obj_t * pOrigPi;
        int t = 0;
        Abc_NtkForEachCi( pNtk, pOrigPi, t ) {
            if ( pOrigPi->Id == pPi->Id ) { origIdx = t; break; }
        }
        if ( origIdx == -1 ) {
            // fallback: use order in cone PI list (best-effort)
            origIdx = j;
            if ( origIdx >= nOrigPis ) origIdx = -1;
        }

        if ( origIdx >= 0 ) {
            // get the CNF variable that encodes this PI in pCnfA/pCnfB
            // Many ABC builds pCnf->pVarNums indexed by AIG object ID:
            // We need Aig_Obj_t* corresponding to this PI; assume pPi->pCopy holds pointer to AIG CI object
            Aig_Obj_t * pAigPi = (Aig_Obj_t*) pPi->pCopy;
            if ( pAigPi ) {
                int varA = pCnfA->pVarNums[ pAigPi->Id ];
                int varB = pCnfB->pVarNums[ pAigPi->Id ];
                piVarA[origIdx] = varA;
                piVarB[origIdx] = varB;
            } else {
                // If pCopy not set, we may try to use pPi->Id as index (some ABC versions use this)
                if ( pPi->Id < pCnfA->nVars ) {
                    piVarA[origIdx] = pPi->Id;
                    piVarB[origIdx] = pPi->Id + pCnfA->nVars;
                }
            }
        }
    }

    // If xi not in cone => independent
    if ( iPi < 0 || iPi >= nOrigPis || piVarA[iPi] == -1 ) {
        Abc_Print( 1, "independent\n" );
        // cleanup
        Cnf_DataFree( pCnfA );
        Cnf_DataFree( pCnfB );
        sat_solver_delete( pSat );
        Aig_ManStop( pAig );
        if ( pConeAig != pCone ) Abc_NtkDelete( pConeAig );
        Abc_NtkDelete( pCone );
        ABC_FREE( piVarA );
        ABC_FREE( piVarB );
        return;
    }

    // Add equality constraints for all PI t != iPi: (vA == vB) as two clauses (¬vA ∨ vB) & (vA ∨ ¬vB)
    // Helper to convert var to SAT literal:
    // Many ABC versions provide Abc_Var2Lit(var, sign). If not present, use this macro:
    #ifndef Abc_Var2Lit
    #define LIT(var, sign) ( ((var) << 1) ^ (sign) )
    #else
    #define LIT Abc_Var2Lit
    #endif

    // Note: sat_solver_addclause expects array of lit (type 'lit' or int). We will use int.
    for ( int t = 0; t < nOrigPis; ++t ) {
        if ( t == iPi ) continue;
        if ( piVarA[t] == -1 || piVarB[t] == -1 ) continue;
        int lit1 = LIT( piVarA[t], 1 ); // ¬vA
        int lit2 = LIT( piVarB[t], 0 ); //  vB
        int arr1[2] = { lit1, lit2 };
        sat_solver_addclause( pSat, arr1, arr1 + 2 );

        int lit3 = LIT( piVarA[t], 0 ); // vA
        int lit4 = LIT( piVarB[t], 1 ); // ¬vB
        int arr2[2] = { lit3, lit4 };
        sat_solver_addclause( pSat, arr2, arr2 + 2 );
    }

    // Prepare var indices for xi and y (output)
    int varXiA = piVarA[iPi];
    int varXiB = piVarB[iPi];
    // Find output literal (the cone has single PO, corresponding to pAig's CO)
    // pAig's CO id mapping: pAig outputs usually at last CO object index; but pCnfA->pVarNums[pObj->Id] maps object id to CNF var
    // We need AIG object for PO. Easiest: find the AIG CO Aig_Obj_t* for the cone's PO:
    Aig_Obj_t * pAigPo = Aig_ManCo( pAig, 0 ); // cone has single output
    int varYA = pCnfA->pVarNums[ pAigPo->Id ];
    int varYB = pCnfB->pVarNums[ pAigPo->Id ];

    // Now check badNeg (f(0,a)=0, f(1,a)=1) => xiA=0 xiB=1 yA=0 yB=1
    int assumptions[4];
    // use LIT macro on variables to build assumption literals
    assumptions[0] = LIT( varXiA, 1 ); // xiA = 0
    assumptions[1] = LIT( varXiB, 0 ); // xiB = 1
    assumptions[2] = LIT( varYA,   1 ); // yA = 0
    assumptions[3] = LIT( varYB,   0 ); // yB = 1

    int ret;
    // sat_solver_solve signature: (s, begin, end, nConfLimit, nInsLimit, nConfLimitGlobal, nInsLimitGlobal)
    ret = sat_solver_solve( pSat, assumptions, assumptions + 4, 0, 0, 0, 0 );
    int badNegSat = 0, badPosSat = 0;
    char * pat1 = NULL, * pat2 = NULL;
    if ( ret == l_True ) {
        badNegSat = 1;
        pat1 = Lsv_SatPatternFromModel( pSat, piVarA, nOrigPis, iPi );
    }

    // badPos: xiA=0 xiB=1 yA=1 yB=0  (f(0,a)=1, f(1,a)=0)
    assumptions[0] = LIT( varXiA, 1 ); // xiA = 0
    assumptions[1] = LIT( varXiB, 0 ); // xiB = 1
    assumptions[2] = LIT( varYA,   0 ); // yA = 1
    assumptions[3] = LIT( varYB,   1 ); // yB = 0

    ret = sat_solver_solve( pSat, assumptions, assumptions + 4, 0, 0, 0, 0 );
    if ( ret == l_True ) {
        badPosSat = 1;
        pat2 = Lsv_SatPatternFromModel( pSat, piVarA, nOrigPis, iPi );
    }

    // Interpret results
    if ( !badPosSat && !badNegSat ) {
        Abc_Print( 1, "independent\n" );
    } else if ( !badPosSat && badNegSat ) {
        Abc_Print( 1, "positive unate\n" );
    } else if ( badPosSat && !badNegSat ) {
        Abc_Print( 1, "negative unate\n" );
    } else {
        Abc_Print( 1, "binate\n" );
        if ( pat1 ) { Abc_Print( 1, "%s\n", pat1 ); ABC_FREE( pat1 ); }
        if ( pat2 ) { Abc_Print( 1, "%s\n", pat2 ); ABC_FREE( pat2 ); }
    }

    // cleanup
    ABC_FREE( piVarA ); ABC_FREE( piVarB );
    if ( pat1 ) ABC_FREE( pat1 );
    if ( pat2 ) ABC_FREE( pat2 );

    Cnf_DataFree( pCnfA );
    Cnf_DataFree( pCnfB );
    sat_solver_delete( pSat );
    Aig_ManStop( pAig );
    if ( pConeAig != pCone ) Abc_NtkDelete( pConeAig );
    Abc_NtkDelete( pCone );
}
