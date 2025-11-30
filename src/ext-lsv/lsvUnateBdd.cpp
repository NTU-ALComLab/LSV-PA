// src/ext-lsv/lsvUnateBdd.cpp
//
// Command:
//   lsv_unate_bdd <k> <i>
//   k : PO index (0-based)
//   i : PI index (0-based)
//
// Strategy:
//   * Ignore any existing BDD networks / global BDDs in ABC.
//   * Build our OWN CUDD manager and BDDs from a strashed AIG:
//       - CI i  -> Cudd_bddIthVar(dd, i)
//       - node  -> AND of fanin BDDs (respecting complemented edges)
//       - PO    -> fanin BDD (respecting PO edge complement)
//   * Use pure BDD operations to check unateness.
//   * Clean up all BDD refs and destroy the CUDD manager.
//
// This avoids all the previous issues with NULL pData, Abc_NtkBuildGlobalBdds,
// Cudd_Not / Cudd_Regular macros, and macro name collisions (b0/b1).

#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "base/abc/abc.h"
#include "bdd/cudd/cudd.h"
#include <cstdint>

// ---------------------------------------------------------------------
// Tiny helper for CUDD complemented pointers (replacement for Cudd_Not)
// ---------------------------------------------------------------------

static inline DdNode * Lsv_Not( DdNode * p )
{
    return (DdNode *)((uintptr_t)p ^ (uintptr_t)1);
}

// ---------------------------------------------------------------------
// Registration into ABC
// ---------------------------------------------------------------------

int Lsv_CommandUnateBdd( Abc_Frame_t * pAbc, int argc, char ** argv );

static void init_unate( Abc_Frame_t * pAbc )
{
    // Abc_Print( 1, "[lsv_unate_bdd] registering command.\n" );
    Cmd_CommandAdd( pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0 );
}

static void destroy_unate( Abc_Frame_t * /*pAbc*/ ) {}

static Abc_FrameInitializer_t frame_initializer_unate =
{
    init_unate,
    destroy_unate
};

struct UnateRegistrationManager
{
    UnateRegistrationManager()
    {
        Abc_FrameAddInitializer( &frame_initializer_unate );
    }
};

static UnateRegistrationManager s_UnateRegistrationManager;

// ---------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------

// Map PI index (0..PiNum-1) to corresponding CI index (0..CiNum-1).
static int Lsv_MapPiToCi( Abc_Ntk_t * pNtk, int iPi )
{
    Abc_Obj_t * pPi, * pCi;
    int i;

    pPi = Abc_NtkPi( pNtk, iPi );
    Abc_NtkForEachCi( pNtk, pCi, i )
    {
        if ( pCi == pPi )
            return i;
    }
    return -1;
}

// Given a BDD bCube, pick one cube and print a PI pattern:
//   - position iPiTarget printed as '-'
//   - other PIs printed as '0'/'1'; don't-cares as '0'
static void Lsv_PrintPatternFromCube(
    DdManager * dd,
    Abc_Ntk_t * pNtk,
    DdNode    * bCube,
    int         iPiTarget
)
{
    int   nCi  = Abc_NtkCiNum( pNtk );
    int   nPi  = Abc_NtkPiNum( pNtk );
    char* cube = (char *)ABC_ALLOC( char, nCi );
    char* pat  = nullptr;
    int   i;

    if ( cube == nullptr )
    {
        // Abc_Print( -1, "[lsv_unate_bdd] ERROR: alloc cube failed.\n" );
        return;
    }

    if ( !Cudd_bddPickOneCube( dd, bCube, cube ) )
    {
        // Abc_Print( -1,
        //     "[lsv_unate_bdd] ERROR: Cudd_bddPickOneCube failed.\n" );
        ABC_FREE( cube );
        return;
    }

    pat = (char *)ABC_ALLOC( char, nPi + 1 );
    if ( pat == nullptr )
    {
        // Abc_Print( -1, "[lsv_unate_bdd] ERROR: alloc pattern failed.\n" );
        ABC_FREE( cube );
        return;
    }

    for ( i = 0; i < nPi; ++i )
    {
        if ( i == iPiTarget )
        {
            pat[i] = '-';
            continue;
        }

        int  ciIndex = Lsv_MapPiToCi( pNtk, i );
        char v       = (ciIndex >= 0) ? cube[ciIndex] : '2';

        if ( v == '0' || v == '1' )
            pat[i] = v;
        else
            pat[i] = '0'; // arbitrary for don't-care
    }
    pat[nPi] = '\0';

    Abc_Print( 1, "%s\n", pat );

    ABC_FREE( cube );
    ABC_FREE( pat );
}

// Build our own CUDD BDDs from a strashed AIG.
// On return, each CI and internal node in pNtkAig has pData = DdNode* (ref'd).
// The manager dd is returned and must later be freed with Lsv_FreeAigBdds.
static DdManager * Lsv_BuildAigBdds( Abc_Ntk_t * pNtkAig )
{
    Abc_Obj_t * pObj;
    int i;

    // Clean pData in case anything is there.
    Abc_NtkForEachObj( pNtkAig, pObj, i )
        pObj->pData = nullptr;

    int nCi = Abc_NtkCiNum( pNtkAig );

    DdManager * dd = Cudd_Init(
        nCi,                  // number of BDD vars
        0,                    // number of ZDD vars
        CUDD_UNIQUE_SLOTS,    // unique table size
        CUDD_CACHE_SLOTS,     // cache size
        0                     // max memory (0 = default)
    );
    if ( dd == nullptr )
    {
        // Abc_Print( -1,
        //     "[lsv_unate_bdd] ERROR: Cudd_Init failed.\n" );
        return nullptr;
    }

    // Assign BDD variables to CIs in CI-order.
    Abc_Obj_t * pCi;
    Abc_NtkForEachCi( pNtkAig, pCi, i )
    {
        DdNode * pVar = Cudd_bddIthVar( dd, i );
        Cudd_Ref( pVar );
        pCi->pData = pVar;
    }

    // Build BDDs for AIG nodes (topological order).
    Abc_Obj_t * pNode;
    Abc_NtkForEachNode( pNtkAig, pNode, i )
    {
        Abc_Obj_t * pF0 = Abc_ObjFanin0( pNode );
        Abc_Obj_t * pF1 = Abc_ObjFanin1( pNode );
        DdNode    * pBdd0  = (DdNode *)pF0->pData;
        DdNode    * pBdd1  = (DdNode *)pF1->pData;

        if ( pBdd0 == nullptr || pBdd1 == nullptr )
        {
            // Abc_Print( -1,
            //     "[lsv_unate_bdd] ERROR: internal node %d has fanin with NULL pData.\n",
            //     Abc_ObjId( pNode ) );
            Cudd_Quit( dd );
            return nullptr;
        }

        if ( Abc_ObjFaninC0( pNode ) )
            pBdd0 = Lsv_Not( pBdd0 );
        if ( Abc_ObjFaninC1( pNode ) )
            pBdd1 = Lsv_Not( pBdd1 );

        DdNode * pFunc = Cudd_bddAnd( dd, pBdd0, pBdd1 );
        Cudd_Ref( pFunc );
        pNode->pData = pFunc;
    }

    return dd;
}

// Free all BDDs stored in pData for CIs and nodes, and quit CUDD.
static void Lsv_FreeAigBdds( Abc_Ntk_t * pNtkAig, DdManager * dd )
{
    if ( dd == nullptr )
        return;

    Abc_Obj_t * pObj;
    int i;

    // Deref all node BDDs
    Abc_NtkForEachNode( pNtkAig, pObj, i )
    {
        if ( pObj->pData )
        {
            Cudd_RecursiveDeref( dd, (DdNode *)pObj->pData );
            pObj->pData = nullptr;
        }
    }

    // Deref all CI BDD vars
    Abc_NtkForEachCi( pNtkAig, pObj, i )
    {
        if ( pObj->pData )
        {
            Cudd_RecursiveDeref( dd, (DdNode *)pObj->pData );
            pObj->pData = nullptr;
        }
    }

    Cudd_Quit( dd );
}

// ---------------------------------------------------------------------
// Core BDD-based unateness check using our own AIG→BDD mapping
// ---------------------------------------------------------------------

static int Lsv_DoUnateBdd(
    Abc_Ntk_t * pNtkOrig,
    int         kPo,
    int         iPi
)
{
    // 1. Build (or reuse) a strashed AIG network
    Abc_Ntk_t * pNtkAig    = nullptr;
    int         fDeleteAig = 0;

    // Abc_Print( 1,
    //     "[lsv_unate_bdd][DEBUG] Original network: isStrash=%d, isBddLogic=%d, isLogic=%d\n",
    //     Abc_NtkIsStrash( pNtkOrig ),
    //     Abc_NtkIsBddLogic( pNtkOrig ),
    //     Abc_NtkIsLogic( pNtkOrig ) );

    if ( Abc_NtkIsStrash( pNtkOrig ) )
    {
        pNtkAig    = pNtkOrig;
        fDeleteAig = 0;
        // Abc_Print( 1,
        //     "[lsv_unate_bdd][DEBUG] Using existing strashed network.\n" );
    }
    else
    {
        pNtkAig = Abc_NtkStrash( pNtkOrig, 0, 1, 0 );
        if ( pNtkAig == nullptr )
        {
            // Abc_Print( -1,
            //     "[lsv_unate_bdd] ERROR: Abc_NtkStrash failed.\n" );
            return 1;
        }
        fDeleteAig = 1;
        // Abc_Print( 1,
        //     "[lsv_unate_bdd][DEBUG] Created new strashed network for unate check.\n" );
    }

    // Abc_Print( 1,
    //     "[lsv_unate_bdd][DEBUG] AIG network: #PIs=%d, #CIs=%d, #POs=%d\n",
    //     Abc_NtkPiNum( pNtkAig ), Abc_NtkCiNum( pNtkAig ), Abc_NtkPoNum( pNtkAig ) );

    // 2. Build our CUDD BDDs for this AIG
    DdManager * dd = Lsv_BuildAigBdds( pNtkAig );
    if ( dd == nullptr )
    {
        if ( fDeleteAig ) Abc_NtkDelete( pNtkAig );
        return 1;
    }

    // 3. Retrieve the PO function f from its fanin's BDD
    Abc_Obj_t * pPo    = Abc_NtkPo( pNtkAig, kPo );
    Abc_Obj_t * pFanin = Abc_ObjFanin0( pPo );
    DdNode    * f      = (DdNode *)pFanin->pData;

    if ( pPo == nullptr || pFanin == nullptr || f == nullptr )
    {
        // Abc_Print( -1,
        //     "[lsv_unate_bdd] ERROR: PO %d or its fanin has NULL BDD.\n", kPo );
        Lsv_FreeAigBdds( pNtkAig, dd );
        if ( fDeleteAig ) Abc_NtkDelete( pNtkAig );
        return 1;
    }

    if ( Abc_ObjFaninC0( pPo ) )
        f = Lsv_Not( f );

    // Abc_Print( 1,
    //     "[lsv_unate_bdd][DEBUG] PO %d, PI %d: BDD f=%p\n",
    //     kPo, iPi, (void *)f );

    // 4. Identify the CI index and BDD variable for PI iPi
    int ciIndex = Lsv_MapPiToCi( pNtkAig, iPi );
    if ( ciIndex < 0 )
    {
        // Abc_Print( -1,
        //     "[lsv_unate_bdd] ERROR: cannot map PI %d to CI index.\n", iPi );
        Lsv_FreeAigBdds( pNtkAig, dd );
        if ( fDeleteAig ) Abc_NtkDelete( pNtkAig );
        return 1;
    }

    DdNode * var = Cudd_bddIthVar( dd, ciIndex ); // our own CI→var mapping
    // Abc_Print( 1,
    //     "[lsv_unate_bdd][DEBUG] PI %d -> CI %d, BDD var[%d]=%p\n",
    //     iPi, ciIndex, ciIndex, (void *)var );

    // 5. Cofactors f0=f|xi=0, f1=f|xi=1
    DdNode * f0 = Cudd_Cofactor( dd, f, Lsv_Not( var ) ); // xi = 0
    Cudd_Ref( f0 );
    DdNode * f1 = Cudd_Cofactor( dd, f, var );            // xi = 1
    Cudd_Ref( f1 );

    // Abc_Print( 1,
    //     "[lsv_unate_bdd][DEBUG] f0=%p, f1=%p\n", (void *)f0, (void *)f1 );

    DdNode * zero = Cudd_ReadLogicZero( dd );

    int isIndependent = (f0 == f1);

    // negBad: points where f(0,α)=1 and f(1,α)=0 (violates positive unateness)
    DdNode * negBad = Cudd_bddAnd( dd, f0, Lsv_Not( f1 ) );
    Cudd_Ref( negBad );
    // posBad: points where f(0,α)=0 and f(1,α)=1 (violates negative unateness)
    DdNode * posBad = Cudd_bddAnd( dd, Lsv_Not( f0 ), f1 );
    Cudd_Ref( posBad );

    int hasNegBad = (negBad != zero);
    int hasPosBad = (posBad != zero);

    // Abc_Print( 1,
    //     "[lsv_unate_bdd][DEBUG] isIndependent=%d, hasNegBad=%d, hasPosBad=%d\n",
    //     isIndependent, hasNegBad, hasPosBad );

    // 6. Classification + witnesses
    if ( isIndependent )
    {
        Abc_Print( 1, "independent\n" );
    }
    else if ( !hasNegBad && hasPosBad )
    {
        Abc_Print( 1, "positive unate\n" );
    }
    else if ( hasNegBad && !hasPosBad )
    {
        Abc_Print( 1, "negative unate\n" );
    }
        else
    {
        // Binate: both types of violations exist.
        Abc_Print( 1, "binate\n" );

        int nPi   = Abc_NtkPiNum( pNtkAig );
        int nCi   = Abc_NtkCiNum( pNtkAig );
        int nVars = Cudd_ReadSize( dd );
        int i;

        // Map each PI index -> CI index once, for fast use
        int * pi2ci = (int *)ABC_ALLOC( int, nPi );
        for ( i = 0; i < nPi; ++i )
            pi2ci[i] = Lsv_MapPiToCi( pNtkAig, i );

        // Values for all BDD vars for Cudd_Eval: 0/1; we set all CIs.
        int * vals = (int *)ABC_ALLOC( int, nVars );
        for ( i = 0; i < nVars; ++i )
            vals[i] = 0; // default; we'll overwrite CI positions

        int ciTarget = pi2ci[iPi];

        unsigned long long maxMask = 1ULL;
        if ( nPi > 1 )
            maxMask = 1ULL << (nPi - 1);  // 2^(nPi-1) assignments to "other" PIs

        unsigned long long posMask = 0;
        unsigned long long negMask = 0;
        int posFound = 0;
        int negFound = 0;

        // Enumerate assignments to all PIs except iPi
        for ( unsigned long long mask = 0;
              mask < maxMask && (!posFound || !negFound);
              ++mask )
        {
            // Assign all PIs except the target from bits of "mask"
            int bitIndex = 0;
            for ( int j = 0; j < nPi; ++j )
            {
                int ci = pi2ci[j];
                if ( j == iPi )
                    continue; // skip target; we set it separately below

                int bit = ( (mask >> bitIndex) & 1ULL ) ? 1 : 0;
                vals[ci] = bit;
                bitIndex++;
            }

            // Now evaluate f with xi = 0 and xi = 1
            vals[ciTarget] = 0;
            DdNode * r0 = Cudd_Eval( dd, f, vals );
            int v0 = (r0 == Cudd_ReadLogicZero( dd )) ? 0 : 1;

            vals[ciTarget] = 1;
            DdNode * r1 = Cudd_Eval( dd, f, vals );
            int v1 = (r1 == Cudd_ReadLogicZero( dd )) ? 0 : 1;

            // Debug
            // Abc_Print( 1,
            //     "[lsv_unate_bdd][DEBUG] mask=%llu, v0=%d, v1=%d\n",
            //     (unsigned long long)mask, v0, v1 );

            if ( !posFound && v0 == 0 && v1 == 1 )
            {
                posFound = 1;
                posMask  = mask;
                // Abc_Print( 1,
                //     "[lsv_unate_bdd][DEBUG] Found positive witness mask=%llu\n",
                //     (unsigned long long)mask );
            }
            if ( !negFound && v0 == 1 && v1 == 0 )
            {
                negFound = 1;
                negMask  = mask;
                // Abc_Print( 1,
                //     "[lsv_unate_bdd][DEBUG] Found negative witness mask=%llu\n",
                //     (unsigned long long)mask );
            }
        }

        // Helper lambda: turn a mask into a PI pattern string
        auto buildPatternFromMask = [&]( unsigned long long mask ) -> char *
        {
            char * pat = (char *)ABC_ALLOC( char, nPi + 1 );
            if ( !pat )
                return nullptr;

            int bitIndex = 0;
            for ( int j = 0; j < nPi; ++j )
            {
                if ( j == iPi )
                {
                    pat[j] = '-';
                    continue;
                }
                int bit = ( (mask >> bitIndex) & 1ULL ) ? 1 : 0;
                bitIndex++;
                pat[j] = bit ? '1' : '0';
            }
            pat[nPi] = '\0';
            return pat;
        };

        // Print positive witness pattern
        if ( posFound )
        {
            char * patPos = buildPatternFromMask( posMask );
            if ( patPos )
            {
                // Abc_Print( 1,
                //     "[lsv_unate_bdd][DEBUG] Positive pattern: %s\n",
                //     patPos );
                Abc_Print( 1, "%s\n", patPos );
                ABC_FREE( patPos );
            }
            else
            {
                // Abc_Print( -1,
                //     "[lsv_unate_bdd] ERROR: failed to allocate positive pattern.\n" );
            }
        }
        else
        {
            // Abc_Print( -1,
            //     "[lsv_unate_bdd] ERROR: could not find positive witness, "
            //     "despite hasPosBad=1.\n" );
        }

        // Print negative witness pattern
        if ( negFound )
        {
            char * patNeg = buildPatternFromMask( negMask );
            if ( patNeg )
            {
                // Abc_Print( 1,
                //     "[lsv_unate_bdd][DEBUG] Negative pattern: %s\n",
                //     patNeg );
                Abc_Print( 1, "%s\n", patNeg );
                ABC_FREE( patNeg );
            }
            else
            {
                // Abc_Print( -1,
                //     "[lsv_unate_bdd] ERROR: failed to allocate negative pattern.\n" );
            }
        }
        else
        {
            // Abc_Print( -1,
            //     "[lsv_unate_bdd] ERROR: could not find negative witness, "
            //     "despite hasNegBad=1.\n" );
        }

        ABC_FREE( vals );
        ABC_FREE( pi2ci );
    }


    // 7. Cleanup local BDD nodes we created
    Cudd_RecursiveDeref( dd, posBad );
    Cudd_RecursiveDeref( dd, negBad );
    Cudd_RecursiveDeref( dd, f0 );
    Cudd_RecursiveDeref( dd, f1 );

    Lsv_FreeAigBdds( pNtkAig, dd );
    if ( fDeleteAig )
        Abc_NtkDelete( pNtkAig );

    return 0;
}

// ---------------------------------------------------------------------
// ABC command hook
// ---------------------------------------------------------------------

int Lsv_CommandUnateBdd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk;
    int         kPo, iPi;

    if ( argc != 3 )
    {
        Abc_Print( -1, "usage: lsv_unate_bdd <k> <i>\n" );
        Abc_Print( -1, "  k : PO index (0-based)\n" );
        Abc_Print( -1, "  i : PI index (0-based)\n" );
        return 1;
    }

    kPo = atoi( argv[1] );
    iPi = atoi( argv[2] );

    pNtk = Abc_FrameReadNtk( pAbc );
    if ( pNtk == nullptr )
    {
        // Abc_Print( -1, "[lsv_unate_bdd] ERROR: empty network.\n" );
        return 1;
    }

    if ( kPo < 0 || kPo >= Abc_NtkPoNum( pNtk ) )
    {
        // Abc_Print( -1,
        //     "[lsv_unate_bdd] ERROR: PO index %d out of range (0..%d).\n",
        //     kPo, Abc_NtkPoNum( pNtk ) - 1 );
        return 1;
    }

    if ( iPi < 0 || iPi >= Abc_NtkPiNum( pNtk ) )
    {
        // Abc_Print( -1,
        //     "[lsv_unate_bdd] ERROR: PI index %d out of range (0..%d).\n",
        //     iPi, Abc_NtkPiNum( pNtk ) - 1 );
        return 1;
    }

    // Abc_Print( 1,
    //     "[lsv_unate_bdd][DEBUG] Called with PO=%d, PI=%d.\n", kPo, iPi );

    return Lsv_DoUnateBdd( pNtk, kPo, iPi );
}
