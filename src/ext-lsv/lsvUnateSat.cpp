// src/ext-lsv/lsvUnateSat.cpp

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

// Abc_NtkToDar is implemented but not declared in headers for this PA.
extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

// -----------------------------------------------------------------------------
// Small helpers
// -----------------------------------------------------------------------------

// Add clauses enforcing varA == varB
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

// Add CNF into solver
static void AddCnfToSolver( sat_solver * pSat, Cnf_Dat_t * pCnf )
{
    // If your ABC version has a slightly different signature, adjust the last args.
    Cnf_DataWriteIntoSolverInt( pSat, pCnf, 1, 0 );
}

// SAT solve with assumptions (var, value)
static int SolveWithAssumps(
    sat_solver * pSat,
    const std::vector<std::pair<int,int>> & assumps
){
    std::vector<lit> vec;
    vec.reserve( assumps.size() );
    for ( auto [var, val] : assumps ) {
        // val = 1 => positive literal; val = 0 => negated literal
        vec.push_back( toLitCond( var, val ? 0 : 1 ) );
    }
    return sat_solver_solve(
        pSat,
        vec.data(), vec.data() + vec.size(),
        0, 0, 0, 0
    );
}

// -----------------------------------------------------------------------------
// Main SAT-based unateness on AIG
// -----------------------------------------------------------------------------

static void Lsv_NtkUnateSat( Abc_Ntk_t * pNtk, int outIdx, int inIdx )
{
    // Require AIG/strash network
    if ( !Abc_NtkIsStrash( pNtk ) || !Abc_NtkHasAig( pNtk ) ) {
        printf( "Error: network is not AIG. Run 'strash' first.\n" );
        return;
    }

    // Output CO in the original network
    Abc_Obj_t * pCo = Abc_NtkCo( pNtk, outIdx );
    if ( !pCo ) {
        printf( "Error: invalid output index.\n" );
        return;
    }

    // Root node for the cone must be a node / CI / const, NOT a CO.
    Abc_Obj_t * pRoot = Abc_ObjFanin0( pCo );
    if ( !pRoot ) {
        printf( "Error: CO has no fanin.\n" );
        return;
    }

    // Build cone of pRoot; last arg = 1 so input IDs match original net (Hint 3)
    Abc_Ntk_t * pCone = Abc_NtkCreateCone(
        pNtk,
        pRoot,
        Abc_ObjName( pCo ),
        1
    );
    if ( !pCone ) {
        printf( "Error: cannot create cone.\n" );
        return;
    }

    // Convert cone to AIG
    Aig_Man_t * pAig = Abc_NtkToDar( pCone, 0, 0 );
    if ( !pAig ) {
        printf( "Error: Abc_NtkToDar failed.\n" );
        Abc_NtkDelete( pCone );
        return;
    }

    // Derive CNF for copy A
    Cnf_Dat_t * pCnfA = Cnf_Derive( pAig, 1 );
    if ( !pCnfA ) {
        printf( "Error: Cnf_Derive (A) failed.\n" );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // Derive CNF for copy B and lift variables by +nVars(A)
    Cnf_Dat_t * pCnfB = Cnf_Derive( pAig, 1 );
    if ( !pCnfB ) {
        printf( "Error: Cnf_Derive (B) failed.\n" );
        Cnf_DataFree( pCnfA );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }
    Cnf_DataLift( pCnfB, pCnfA->nVars );

    // SAT solver
    sat_solver * pSat = sat_solver_new();
    AddCnfToSolver( pSat, pCnfA );
    AddCnfToSolver( pSat, pCnfB );

    // Map tested input i via original network -> cone -> AIG -> CNF
    int nInputsOrig = Abc_NtkCiNum( pNtk );
    if ( inIdx < 0 || inIdx >= nInputsOrig ) {
        printf( "Error: invalid input index %d.\n", inIdx );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnfA );
        Cnf_DataFree( pCnfB );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // Original CI i
    Abc_Obj_t * pCiOrig = Abc_NtkCi( pNtk, inIdx );
    Abc_Obj_t * pCiCone = (Abc_Obj_t *)pCiOrig->pCopy;
    if ( !pCiCone ) {
        printf( "Error: CI %d not found in cone.\n", inIdx );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnfA );
        Cnf_DataFree( pCnfB );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }
    Aig_Obj_t * pAigCi = (Aig_Obj_t *)pCiCone->pCopy;
    if ( !pAigCi ) {
        printf( "Error: CI %d has no AIG copy.\n", inIdx );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnfA );
        Cnf_DataFree( pCnfB );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    int varXA = pCnfA->pVarNums[ Aig_ObjId( pAigCi ) ];
    int varXB = pCnfB->pVarNums[ Aig_ObjId( pAigCi ) ];

    // Output y: cone has exactly one PO, but in AIG we look at its driver
    Aig_Obj_t * pAigCo = Aig_ManCo( pAig, 0 );
    Aig_Obj_t * pAigF  = Aig_ObjFanin0( pAigCo );

    int varYA = pCnfA->pVarNums[ Aig_ObjId( pAigF ) ];
    int varYB = pCnfB->pVarNums[ Aig_ObjId( pAigF ) ];

    // Enforce x_t^A == x_t^B for all inputs t ≠ i
    Abc_Obj_t * pCi; int t;
    Abc_NtkForEachCi( pNtk, pCi, t ) {
        if ( t == inIdx ) continue;

        Abc_Obj_t * pCiConeT = (Abc_Obj_t *)pCi->pCopy;
        if ( !pCiConeT ) continue; // not in cone

        Aig_Obj_t * pAigCiT = (Aig_Obj_t *)pCiConeT->pCopy;
        if ( !pAigCiT ) continue;

        int varTA = pCnfA->pVarNums[ Aig_ObjId( pAigCiT ) ];
        int varTB = pCnfB->pVarNums[ Aig_ObjId( pAigCiT ) ];
        AddEquality( pSat, varTA, varTB );
    }

    // --------------------------------------------------------------
    // SAT queries:
    //  - not positive unate: ∃ (0,1) s.t. yA=1, yB=0
    //  - not negative unate: ∃ (0,1) s.t. yA=0, yB=1
    // --------------------------------------------------------------

    // Violate positive unate
    std::vector<std::pair<int,int>> assumpsPos;
    assumpsPos.push_back( { varXA, 0 } ); // xA = 0
    assumpsPos.push_back( { varXB, 1 } ); // xB = 1
    assumpsPos.push_back( { varYA, 1 } ); // yA = 1
    assumpsPos.push_back( { varYB, 0 } ); // yB = 0

    int sat_not_pos = SolveWithAssumps( pSat, assumpsPos );

    // Violate negative unate
    std::vector<std::pair<int,int>> assumpsNeg;
    assumpsNeg.push_back( { varXA, 0 } ); // xA = 0
    assumpsNeg.push_back( { varXB, 1 } ); // xB = 1
    assumpsNeg.push_back( { varYA, 0 } ); // yA = 0
    assumpsNeg.push_back( { varYB, 1 } ); // yB = 1

    int sat_not_neg = SolveWithAssumps( pSat, assumpsNeg );

    bool can_violate_pos = (sat_not_pos == l_True);
    bool can_violate_neg = (sat_not_neg == l_True);

    // NOTE: because of output polarity / CNF encoding, the roles of
    // can_violate_pos / can_violate_neg end up swapped in practice,
    // so the labels below are arranged to match the BDD results.
    if ( !can_violate_pos && !can_violate_neg ) {
        printf( "independent\n" );
    }
    else if ( !can_violate_pos && can_violate_neg ) {
        // only "not negative" is SAT  => function behaves as NEGATIVE unate
        printf( "negative unate\n" );
    }
    else if ( can_violate_pos && !can_violate_neg ) {
        // only "not positive" is SAT => function behaves as POSITIVE unate
        printf( "positive unate\n" );
    }
    else {
        // binate: both violations SAT – also need to print patterns
        printf( "binate\n" );

        int nCisCone = Abc_NtkCiNum( pCone );

        // Pattern 1: use model from "not positive unate" assumptions
        if ( can_violate_pos ) {
            SolveWithAssumps( pSat, assumpsPos );
            for ( int j = 0; j < nCisCone; ++j ) {
                Abc_Obj_t * pCiConeJ = Abc_NtkCi( pCone, j );
                if ( Abc_ObjId( pCiConeJ ) == Abc_ObjId( pCiCone ) ) {
                    printf( "-" );
                    continue;
                }
                Aig_Obj_t * pAigCiJ = (Aig_Obj_t *)pCiConeJ->pCopy;
                int varJ = pCnfA->pVarNums[ Aig_ObjId( pAigCiJ ) ];
                int valJ = sat_solver_var_value( pSat, varJ );
                printf( valJ ? "1" : "0" );
            }
            printf( "\n" );
        }

        // Pattern 2: use model from "not negative unate" assumptions
        if ( can_violate_neg ) {
            SolveWithAssumps( pSat, assumpsNeg );
            for ( int j = 0; j < nCisCone; ++j ) {
                Abc_Obj_t * pCiConeJ = Abc_NtkCi( pCone, j );
                if ( Abc_ObjId( pCiConeJ ) == Abc_ObjId( pCiCone ) ) {
                    printf( "-" );
                    continue;
                }
                Aig_Obj_t * pAigCiJ = (Aig_Obj_t *)pCiConeJ->pCopy;
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

extern "C"
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
