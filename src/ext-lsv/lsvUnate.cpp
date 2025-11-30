/**
 * @file lsvUnate.cpp
 * @brief BDD Unateness checking for LSV PA2 (Part 1)
 */

#include <vector>
#include <cstdio>
#include <cstdlib>
#include <cstdint>

// Define pointer types if missing in your environment
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

// cubeVals: size = Cudd_ReadSize(dd), entries in {0,1,2} for each BDD var index.
// We must map each primary input x_j to its BDD var index via Abc_ObjGlobalBdd.
static void
Lsv_PrintPattern( DdManager * dd,
                  char * cubeVals,
                  int nVars,
                  Abc_Ntk_t * pNtk,
                  int inputIdx )
{
    int nInputs = Abc_NtkCiNum( pNtk );

    for ( int j = 0; j < nInputs; ++j )
    {
        // Tested input x_i is always printed as '-'
        if ( j == inputIdx ) {
            printf( "-" );
            continue;
        }

        // Get the global BDD for CI j
        Abc_Obj_t * pCi    = Abc_NtkCi( pNtk, j );
        DdNode    * pVarCi = (DdNode *)Abc_ObjGlobalBdd( pCi );

        if ( pVarCi == nullptr ) {
            // Fallback if something goes wrong
            printf( "0" );
            continue;
        }

        int varIdx = Cudd_NodeReadIndex( pVarCi );
        if ( varIdx < 0 || varIdx >= nVars ) {
            printf( "0" );
            continue;
        }

        char v = cubeVals[ varIdx ];
        // 0 = False, 1 = True, 2 = Don't Care (we print DC as 0)
        if ( v == 1 )
            printf( "1" );
        else
            printf( "0" );
    }
    printf( "\n" );
}

// -----------------------------------------------------------------------------
// Main Logic
// -----------------------------------------------------------------------------

void Lsv_NtkUnateBdd( Abc_Ntk_t * pNtk, int outIdx, int inIdx )
{
    // 1. Ensure global BDDs exist by asking for the Co's global BDD
    Abc_Obj_t * pCo   = Abc_NtkCo( pNtk, outIdx );
    DdNode    * pFunc = (DdNode *)Abc_ObjGlobalBdd( pCo );
    if ( pFunc == nullptr ) {
        printf( "Error: Output global BDD is NULL.\n" );
        return;
    }

    // 2. Get BDD manager from the network
    DdManager * dd = (DdManager *)pNtk->pManFunc;
    if ( dd == nullptr ) {
        printf( "Error: BDD manager (pManFunc) is NULL.\n" );
        return;
    }

    // 3. Get the BDD variable for input x_i via its CI node
    Abc_Obj_t * pCi  = Abc_NtkCi( pNtk, inIdx );
    DdNode    * pVar = (DdNode *)Abc_ObjGlobalBdd( pCi );
    if ( pVar == nullptr ) {
        printf( "Error: CI %d has no global BDD variable.\n", inIdx );
        return;
    }

    // NOTE: We do NOT Ref/RecursiveDeref pVar or pFunc – they are owned by ABC.

    // 4. Compute cofactors:
    //    f1 = f | x_i = 1
    //    f0 = f | x_i = 0
    DdNode * f1 = Cudd_Cofactor( dd, pFunc, pVar );            Cudd_Ref( f1 );
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
        printf( "binate\n" );

        // 6. Generate patterns for binate case

        int nVars = Cudd_ReadSize( dd );
        std::vector<char> cubeVals( nVars, 2 ); // all DC initially

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

    // 7. Cleanup cofactors we created
    Cudd_RecursiveDeref( dd, f1 );
    Cudd_RecursiveDeref( dd, f0 );

    fflush( stdout );
}

// -----------------------------------------------------------------------------
// ABC Command Wrapper
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
