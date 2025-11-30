#include <vector>
#include <cstdio>
#include <cstdlib>
#include <cstdint>

extern "C" {
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "aig/aig/aig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
}

#include "lsv.h"

extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

// Tiny helper: build equality clauses (a == b)
static void AddEquality( sat_solver * pSat, int varA, int varB )
{
    // (¬a ∨ b)
    {
        lit lits[2];
        lits[0] = toLitCond( varA, 1 ); // ¬a
        lits[1] = toLitCond( varB, 0 ); //  b
        sat_solver_addclause( pSat, lits, lits + 2 );
    }
    // (a ∨ ¬b)
    {
        lit lits[2];
        lits[0] = toLitCond( varA, 0 ); //  a
        lits[1] = toLitCond( varB, 1 ); // ¬b
        sat_solver_addclause( pSat, lits, lits + 2 );
    }
}

// helper: add CNF to solver, both copies
static void AddCnfToSolver( sat_solver * pSat, Cnf_Dat_t * pCnf )
{
    // Standard ABC utility – if the signature differs slightly in your
    // version, adjust according to cnf.h / satSolver.h.
    Cnf_DataWriteIntoSolverInt( pSat, pCnf, 1, 0 );
}

// Check SAT with a list of assumptions (var,value pairs)
static int SolveWithAssumps( sat_solver * pSat,
                             const std::vector<std::pair<int,int>> & assumps )
{
    std::vector<lit> vec;
    vec.reserve( assumps.size() );
    for ( auto [var, val] : assumps ) {
        vec.push_back( toLitCond( var, val ? 0 : 1 ) ); // val=1 ⇒ positive literal
    }
    // Signature may differ; adjust extra parms if needed.
    return sat_solver_solve( pSat,
                             vec.data(), vec.data() + vec.size(),
                             0, 0, 0, 0 );
}

// Main SAT-based unateness check on AIG
static void Lsv_NtkUnateSat( Abc_Ntk_t * pNtk, int outIdx, int inIdx )
{
    // 0. Preconditions: AIG network
    if ( !Abc_NtkIsStrash( pNtk ) || !Abc_NtkHasAig( pNtk ) ) {
        printf( "Error: network is not AIG. Run 'strash' first.\n" );
        return;
    }

    // 1. Build cone of the selected output (optional but matches the hint).
    Abc_Obj_t * pCo = Abc_NtkCo( pNtk, outIdx );
    if ( !pCo ) {
        printf( "Error: invalid output index.\n" );
        return;
    }

    // last parameter = 1 so that input IDs match originals (Hint 3)
    // Signature of Abc_NtkCreateCone may take 4 args in your ABC:
    //   Abc_Ntk_t * Abc_NtkCreateCone( Abc_Ntk_t * pNtk,
    //                                  Abc_Obj_t * pRoot,
    //                                  char * pName,
    //                                  int fIncludeAllPis );
    Abc_Ntk_t * pCone = Abc_NtkCreateCone(
        pNtk,
        pCo,
        Abc_ObjName( pCo ),
        1 // include all PIs (IDs match)
    );
    if ( !pCone ) {
        printf( "Error: cannot create cone.\n" );
        return;
    }

    // 2. Convert cone to AIG
    Aig_Man_t * pAig = Abc_NtkToDar( pCone, 0, 0 );
    if ( !pAig ) {
        printf( "Error: Abc_NtkToDar failed.\n" );
        Abc_NtkDelete( pCone );
        return;
    }

    // 3. Derive CNF for copy A
    Cnf_Dat_t * pCnfA = Cnf_Derive( pAig, 1 );
    if ( !pCnfA ) {
        printf( "Error: Cnf_Derive (A) failed.\n" );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // 4. Copy B: same CNF, but variables lifted by +nVars(A)
    Cnf_Dat_t * pCnfB = Cnf_Derive( pAig, 1 );
    if ( !pCnfB ) {
        printf( "Error: Cnf_Derive (B) failed.\n" );
        Cnf_DataFree( pCnfA );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }
    Cnf_DataLift( pCnfB, pCnfA->nVars ); // B-vars = A-vars + nVars(A)

    // 5. Initialize SAT solver and add both CNFs
    sat_solver * pSat = sat_solver_new();
    AddCnfToSolver( pSat, pCnfA );
    AddCnfToSolver( pSat, pCnfB );

    // 6. Map inputs and outputs to CNF var indices

    // Get cone CI pointers (these correspond to AIG inputs)
    int nInputs = Abc_NtkCiNum( pCone );
    if ( inIdx < 0 || inIdx >= nInputs ) {
        printf( "Error: invalid input index %d.\n", inIdx );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnfA );
        Cnf_DataFree( pCnfB );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // CI i (in cone) -> AIG object -> CNF var A/B
    Abc_Obj_t * pCiCone = Abc_NtkCi( pCone, inIdx );
    Aig_Obj_t * pAigCi  = (Aig_Obj_t *)pCiCone->pCopy;

    int varXA = pCnfA->pVarNums[ Aig_ObjId( pAigCi ) ];
    int varXB = pCnfB->pVarNums[ Aig_ObjId( pAigCi ) ];

    // Output y (only one PO in cone)
    // AIG PO is Aig_ManCo(pAig, 0), but the actual driver is its fanin.
    Aig_Obj_t * pAigCo = Aig_ManCo( pAig, 0 );
    Aig_Obj_t * pAigF  = Aig_ObjFanin0( pAigCo );

    int varYA = pCnfA->pVarNums[ Aig_ObjId( pAigF ) ];
    int varYB = pCnfB->pVarNums[ Aig_ObjId( pAigF ) ];

    // 7. For each CI t != i, add equality (x_t^A == x_t^B)
    Abc_Obj_t * pCi; int t;
    Abc_NtkForEachCi( pCone, pCi, t ) {
        if ( t == inIdx ) continue;
        Aig_Obj_t * pAigCiT = (Aig_Obj_t *)pCi->pCopy;
        int varTA = pCnfA->pVarNums[ Aig_ObjId( pAigCiT ) ];
        int varTB = pCnfB->pVarNums[ Aig_ObjId( pAigCiT ) ];
        AddEquality( pSat, varTA, varTB );
    }

    // ----------------------------------------------------------------------
    // SAT queries:
    //  - Violation of positive unate: f(0, X) = 1 and f(1, X) = 0
    //  - Violation of negative unate: f(0, X) = 0 and f(1, X) = 1
    // ----------------------------------------------------------------------

    // Check "not positive unate" (exists (0->1,1->0))
    std::vector<std::pair<int,int>> assumpsPos;
    assumpsPos.push_back( { varXA, 0 } ); // xA = 0
    assumpsPos.push_back( { varXB, 1 } ); // xB = 1
    assumpsPos.push_back( { varYA, 1 } ); // yA = 1
    assumpsPos.push_back( { varYB, 0 } ); // yB = 0

    int sat_not_pos = SolveWithAssumps( pSat, assumpsPos );

    // Check "not negative unate" (exists (0->0,1->1))
    std::vector<std::pair<int,int>> assumpsNeg;
    assumpsNeg.push_back( { varXA, 0 } ); // xA = 0
    assumpsNeg.push_back( { varXB, 1 } ); // xB = 1
    assumpsNeg.push_back( { varYA, 0 } ); // yA = 0
    assumpsNeg.push_back( { varYB, 1 } ); // yB = 1

    int sat_not_neg = SolveWithAssumps( pSat, assumpsNeg );

    // Classification:
    //   if both violations UNSAT ⇒ independent
    //   else if only not_pos UNSAT ⇒ positive unate
    //   else if only not_neg UNSAT ⇒ negative unate
    //   else ⇒ binate (both violations SAT)
    bool can_violate_pos = (sat_not_pos == l_True);
    bool can_violate_neg = (sat_not_neg == l_True);

    if ( !can_violate_pos && !can_violate_neg ) {
        printf( "independent\n" );
    }
    else if ( !can_violate_pos && can_violate_neg ) {
        printf( "positive unate\n" );
    }
    else if ( can_violate_pos && !can_violate_neg ) {
        printf( "negative unate\n" );
    }
    else {
        // binate: need to print two patterns
        printf( "binate\n" );

        // Pattern 1 from violation of positive unate (0,1, yA=1,yB=0)
        if ( can_violate_pos ) {
            SolveWithAssumps( pSat, assumpsPos );
            // back-annotate from SAT model
            // collect input assignment (use model values of CI vars)
            int nCis = Abc_NtkCiNum( pCone );
            for ( int j = 0; j < nCis; ++j ) {
                if ( j == inIdx ) {
                    printf( "-" );
                    continue;
                }
                Abc_Obj_t * pCiJ    = Abc_NtkCi( pCone, j );
                Aig_Obj_t * pAigCiJ = (Aig_Obj_t *)pCiJ->pCopy;

                int varJ = pCnfA->pVarNums[ Aig_ObjId( pAigCiJ ) ];
                int valJ = sat_solver_var_value( pSat, varJ ); // 0/1

                printf( valJ ? "1" : "0" );
            }
            printf( "\n" );
        }

        // Pattern 2 from violation of negative unate (0,1, yA=0,yB=1)
        if ( can_violate_neg ) {
            SolveWithAssumps( pSat, assumpsNeg );
            int nCis = Abc_NtkCiNum( pCone );
            for ( int j = 0; j < nCis; ++j ) {
                if ( j == inIdx ) {
                    printf( "-" );
                    continue;
                }
                Abc_Obj_t * pCiJ    = Abc_NtkCi( pCone, j );
                Aig_Obj_t * pAigCiJ = (Aig_Obj_t *)pCiJ->pCopy;

                int varJ = pCnfA->pVarNums[ Aig_ObjId( pAigCiJ ) ];
                int valJ = sat_solver_var_value( pSat, varJ );

                printf( valJ ? "1" : "0" );
            }
            printf( "\n" );
        }
    }

    // Cleanup
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnfA );
    Cnf_DataFree( pCnfB );
    Aig_ManStop( pAig );
    Abc_NtkDelete( pCone );
}

// -----------------------------------------------------------------------------
// ABC command wrapper
// -----------------------------------------------------------------------------

int Lsv_CommandUnateSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    if ( argc != 3 ) {
        printf( "Usage: lsv_unate_sat <out_index> <in_index>\n" );
        return 1;
    }

    int outIdx = atoi( argv[1] );
    int inIdx  = atoi( argv[2] );

    Abc_Ntk_t * pNtk = Abc_FrameReadNtk( pAbc );
    if ( !pNtk ) {
        printf( "Error: empty network.\n" );
        return 1;
    }

    if ( outIdx < 0 || outIdx >= Abc_NtkCoNum( pNtk ) ) {
        printf( "Error: invalid output index %d.\n", outIdx );
        return 1;
    }
    if ( inIdx < 0 || inIdx >= Abc_NtkCiNum( pNtk ) ) {
        printf( "Error: invalid input index %d.\n", inIdx );
        return 1;
    }

    Lsv_NtkUnateSat( pNtk, outIdx, inIdx );
    return 0;
}
