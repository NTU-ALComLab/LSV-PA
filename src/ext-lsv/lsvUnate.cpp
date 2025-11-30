/**
 * @file lsvUnate.cpp
 * @brief BDD Unateness checking for LSV PA2 (Part 1)
 */

#include <vector>
#include <cstdio>
#include <cstdlib>
#include <cstdint>

// Define pointer types if missing in your environment (Safe for Colab/Linux)
#ifndef ptruint
  typedef uintptr_t ptruint;
#endif
#ifndef ptrint
  typedef intptr_t ptrint;
#endif

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "bdd/cudd/cudd.h"
#include "lsv.h"

// -----------------------------------------------------------------------------
// Helper: Print Pattern
// -----------------------------------------------------------------------------
//
// cubeVals: length = Cudd_ReadSize(dd), entries in {0,1,2} (0 = false, 1 = true,
// 2 = don't care) indexed by BDD variable index.  We assume that the BDD
// variable index for CI j is exactly j, which is consistent with how the BDD
// network is built from "collapse" in this assignment.
//
static void Lsv_PrintPattern(
    DdManager * dd,
    char      * cubeVals,
    int         nVars,
    Abc_Ntk_t * pNtk,
    int         inputIdx
){
    int nInputs = Abc_NtkCiNum( pNtk );

    for ( int j = 0; j < nInputs; ++j ) {
        // The tested input x_i is always printed as "-"
        if ( j == inputIdx ) {
            printf( "-" );
            continue;
        }

        // Map primary input j to BDD variable index j.
        int bddVarIdx = j;

        // Safety check: if there are fewer BDD vars than inputs, just print 0.
        if ( bddVarIdx < 0 || bddVarIdx >= nVars ) {
            printf( "0" );
            continue;
        }

        char v = cubeVals[ bddVarIdx ];
        // Treat don't care as 0 when printing.
        if ( v == 1 )
            printf( "1" );
        else
            printf( "0" );
    }
    printf( "\n" );
}

// -----------------------------------------------------------------------------
// Main BDD unateness checking
// -----------------------------------------------------------------------------

void Lsv_NtkUnateBdd( Abc_Ntk_t * pNtk, int outIdx, int inIdx )
{
    // 1. Get BDD manager from the network
    DdManager * dd = (DdManager *)pNtk->pManFunc;
    if ( dd == nullptr ) {
        printf( "Error: BDD Manager is NULL. Run 'collapse' first.\n" );
        return;
    }

    // 2. Get the BDD variable corresponding to primary input x_i.
    //    We assume Cudd_bddIthVar(dd, inIdx) is the variable for input i.
    DdNode * pVar = Cudd_bddIthVar( dd, inIdx );
    if ( pVar == nullptr ) {
        printf( "Error: Input index %d out of BDD bounds.\n", inIdx );
        return;
    }
    // Keep a temporary reference as Hint 1 suggests.
    Cudd_Ref( pVar );

    // 3. Get the BDD for the chosen output y_k from the driver node's local BDD
    Abc_Obj_t * pCo     = Abc_NtkCo( pNtk, outIdx );
    Abc_Obj_t * pDriver = Abc_ObjFanin0( pCo );
    DdNode    * pFunc   = (DdNode *)pDriver->pData;

    if ( pFunc == nullptr ) {
        printf( "Error: Output BDD is NULL.\n" );
        Cudd_RecursiveDeref( dd, pVar );
        return;
    }

    // 4. Compute cofactors:
    //    f1 = f | x_i = 1
    //    f0 = f | x_i = 0
    DdNode * f1 = Cudd_Cofactor( dd, pFunc, pVar );             Cudd_Ref( f1 );
    DdNode * f0 = Cudd_Cofactor( dd, pFunc, Cudd_Not( pVar ) ); Cudd_Ref( f0 );

    // 5. Classify unateness
    if ( f1 == f0 ) {
        printf( "independent\n" );
    }
    else if ( Cudd_bddLeq( dd, f0, f1 ) ) {
        // f0 <= f1  ⇒ monotone increasing in x_i
        printf( "positive unate\n" );
    }
    else if ( Cudd_bddLeq( dd, f1, f0 ) ) {
        // f1 <= f0  ⇒ monotone decreasing in x_i
        printf( "negative unate\n" );
    }
    else {
        // Otherwise the function is binate in x_i.
        printf( "binate\n" );

        int nVars = Cudd_ReadSize( dd );
        std::vector<char> cubeVals( nVars, 2 ); // start with all don't care

        // Pattern 1: cube in (f1 & !f0) ⇒ cofactor equals x_i
        DdNode * diff1 = Cudd_bddAnd( dd, f1, Cudd_Not( f0 ) ); Cudd_Ref( diff1 );
        if ( diff1 != Cudd_ReadLogicZero( dd ) ) {
            if ( Cudd_bddPickOneCube( dd, diff1, cubeVals.data() ) ) {
                Lsv_PrintPattern( dd, cubeVals.data(), nVars, pNtk, inIdx );
            }
        }
        Cudd_RecursiveDeref( dd, diff1 );

        // Pattern 2: cube in (!f1 & f0) ⇒ cofactor equals ¬x_i
        DdNode * diff2 = Cudd_bddAnd( dd, Cudd_Not( f1 ), f0 ); Cudd_Ref( diff2 );
        if ( diff2 != Cudd_ReadLogicZero( dd ) ) {
            if ( Cudd_bddPickOneCube( dd, diff2, cubeVals.data() ) ) {
                Lsv_PrintPattern( dd, cubeVals.data(), nVars, pNtk, inIdx );
            }
        }
        Cudd_RecursiveDeref( dd, diff2 );
    }

    // 6. Cleanup temporary BDD nodes we created
    Cudd_RecursiveDeref( dd, f1 );
    Cudd_RecursiveDeref( dd, f0 );
    Cudd_RecursiveDeref( dd, pVar );

    fflush( stdout );
}

// -----------------------------------------------------------------------------
// ABC command wrapper
// -----------------------------------------------------------------------------

int Lsv_CommandUnateBdd( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    if ( argc != 3 ) {
        printf( "Usage: lsv_unate_bdd <out_index> <in_index>\n" );
        return 1;
    }

    int outIdx = atoi( argv[1] );
    int inIdx  = atoi( argv[2] );

    Abc_Ntk_t * pNtk = Abc_FrameReadNtk( pAbc );
    if ( pNtk == nullptr ) {
        printf( "Error: Empty network.\n" );
        return 1;
    }

    if ( !Abc_NtkIsBddLogic( pNtk ) ) {
        printf( "Error: Network not in BDD format. Run 'collapse' first.\n" );
        return 1;
    }

    if ( outIdx < 0 || outIdx >= Abc_NtkCoNum( pNtk ) ) {
        printf( "Error: Invalid output index %d.\n", outIdx );
        return 1;
    }
    if ( inIdx < 0 || inIdx >= Abc_NtkCiNum( pNtk ) ) {
        printf( "Error: Invalid input index %d.\n", inIdx );
        return 1;
    }

    Lsv_NtkUnateBdd( pNtk, outIdx, inIdx );
    return 0;
}
