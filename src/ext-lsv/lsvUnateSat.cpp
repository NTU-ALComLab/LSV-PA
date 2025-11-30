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
extern "C" {
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
// 'value' is assignment for the underlying AIG node: 0 or 1.
static int SolveWithAssumps(
    sat_solver * pSat,
    const std::vector<std::pair<int,int>> & assumps
){
    std::vector<lit> vec;
    vec.reserve( assumps.size() );
    for ( auto [var, val] : assumps ) {
        // val = 1 ⇒ variable = 1 ⇒ positive literal
        // val = 0 ⇒ variable = 0 ⇒ negative literal
        vec.push_back( toLitCond( var, val ? 0 : 1 ) );
    }
    // In this ABC build: 0 = SAT, non-zero = UNSAT/other.
    return sat_solver_solve(
        pSat,
        vec.data(), vec.data() + vec.size(),
        0, 0, 0, 0
    );
}

// -----------------------------------------------------------------------------
// Main SAT-based unateness on AIG (Part 2)
// -----------------------------------------------------------------------------

static void Lsv_NtkUnateSat( Abc_Ntk_t * pNtk, int outIdx, int inIdx )
{
    // Require AIG/strash network
    if ( !Abc_NtkIsStrash( pNtk ) || !Abc_NtkHasAig( pNtk ) ) {
        printf( "Error: network is not AIG. Run 'strash' first.\n" );
        return;
    }

    // --- 1. Find output CO in original network ---
    Abc_Obj_t * pCo = Abc_NtkCo( pNtk, outIdx );
    if ( !pCo ) {
        printf( "Error: invalid output index.\n" );
        return;
    }

    // Root node for the cone: the CO's fanin (driver).
    Abc_Obj_t * pRoot = Abc_ObjFanin0( pCo );
    if ( !pRoot ) {
        printf( "Error: CO has no fanin.\n" );
        return;
    }

    // --- 2. Build cone network rooted at pRoot ---
    // last arg = 1 so CI IDs in the cone match original IDs (Hint 3).
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

    // --- 3. Map the tested input index to a CI in the cone by **object ID** ---
    int nInputsOrig = Abc_NtkCiNum( pNtk );
    if ( inIdx < 0 || inIdx >= nInputsOrig ) {
        printf( "Error: invalid input index %d.\n", inIdx );
        Abc_NtkDelete( pCone );
        return;
    }

    Abc_Obj_t * pCiOrig = Abc_NtkCi( pNtk, inIdx );
    int         idOrig  = Abc_ObjId( pCiOrig );

    // Because we used "1" in Abc_NtkCreateCone, the cone contains a CI with same ID.
    Abc_Obj_t * pCiConeTarget = Abc_NtkObj( pCone, idOrig );
    if ( !pCiConeTarget || !Abc_ObjIsCi( pCiConeTarget ) ) {
        printf( "Error: CI %d not found in cone.\n", inIdx );
        Abc_NtkDelete( pCone );
        return;
    }

    // --- 4. Convert cone to AIG and derive CNF (two copies) ---
    Aig_Man_t * pAig = Abc_NtkToDar( pCone, 0, 0 );
    if ( !pAig ) {
        printf( "Error: Abc_NtkToDar failed.\n" );
        Abc_NtkDelete( pCone );
        return;
    }

    Cnf_Dat_t * pCnfA = Cnf_Derive( pAig, 1 );
    if ( !pCnfA ) {
        printf( "Error: Cnf_Derive (A) failed.\n" );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    Cnf_Dat_t * pCnfB = Cnf_Derive( pAig, 1 );
    if ( !pCnfB ) {
        printf( "Error: Cnf_Derive (B) failed.\n" );
        Cnf_DataFree( pCnfA );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }
    Cnf_DataLift( pCnfB, pCnfA->nVars );

    sat_solver * pSat = sat_solver_new();
    AddCnfToSolver( pSat, pCnfA );
    AddCnfToSolver( pSat, pCnfB );

    // --- 5. Map tested input in the cone to AIG & CNF variables ---
    Aig_Obj_t * pAigCi = (Aig_Obj_t *)pCiConeTarget->pCopy;
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

    // --- 6. Logical output g: fanin of the AIG PO (with complement) ---
    Aig_Obj_t * pAigCo = Aig_ManCo( pAig, 0 );
    Aig_Obj_t * pOut   = Aig_ObjFanin0( pAigCo ); // literal representing g

    Aig_Obj_t * pOutReg = Aig_Regular( pOut );
    int         signY   = Aig_IsComplement( pOut ); // 0 = non-inverted, 1 = inverted

    int varYA = pCnfA->pVarNums[ Aig_ObjId( pOutReg ) ];
    int varYB = pCnfB->pVarNums[ Aig_ObjId( pOutReg ) ];

    // --- 7. Enforce equality for all other inputs in the cone ---
    Abc_Obj_t * pCiConeJ;
    int j;
    Abc_NtkForEachCi( pCone, pCiConeJ, j ) {
        if ( Abc_ObjId( pCiConeJ ) == idOrig )
            continue; // skip the tested input

        Aig_Obj_t * pAigCiJ = (Aig_Obj_t *)pCiConeJ->pCopy;
        if ( !pAigCiJ ) continue;

        int varTA = pCnfA->pVarNums[ Aig_ObjId( pAigCiJ ) ];
        int varTB = pCnfB->pVarNums[ Aig_ObjId( pAigCiJ ) ];
        AddEquality( pSat, varTA, varTB );
    }

    // --------------------------------------------------------------
    // 8. SAT queries:
    // For network output g(X), with literal g = (pOutReg, signY):
    //
    //  - not positive unate:
    //      ∃Z   such that  xA=0, xB=1,  g(0,Z)=1, g(1,Z)=0
    //  - not negative unate:
    //      ∃Z   such that  xA=0, xB=1,  g(0,Z)=0, g(1,Z)=1
    //
    // Our CNF variable is for the regular node F = pOutReg.
    // The relationship is:  g = F XOR signY.
    // So to set g = 1, we set F = (1 XOR signY), etc.
    // --------------------------------------------------------------

    // Violate positive unate: gA=1, gB=0
    std::vector<std::pair<int,int>> assumpsPos;
    assumpsPos.push_back( { varXA, 0 } );                 // xA = 0
    assumpsPos.push_back( { varXB, 1 } );                 // xB = 1
    assumpsPos.push_back( { varYA, 1 ^ signY } );         // F_A = gA XOR signY
    assumpsPos.push_back( { varYB, 0 ^ signY } );         // F_B = gB XOR signY

    int sat_not_pos = SolveWithAssumps( pSat, assumpsPos );

    // Violate negative unate: gA=0, gB=1
    std::vector<std::pair<int,int>> assumpsNeg;
    assumpsNeg.push_back( { varXA, 0 } );                 // xA = 0
    assumpsNeg.push_back( { varXB, 1 } );                 // xB = 1
    assumpsNeg.push_back( { varYA, 0 ^ signY } );         // F_A = gA XOR signY
    assumpsNeg.push_back( { varYB, 1 ^ signY } );         // F_B = gB XOR signY

    int sat_not_neg = SolveWithAssumps( pSat, assumpsNeg );

    // sat_solver_solve(...) == 0  ⇔ SAT  (violating witness exists)
    bool can_violate_pos = (sat_not_pos == 0);
    bool can_violate_neg = (sat_not_neg == 0);

    // --------------------------------------------------------------
    // 9. Classification:
    //  - P = can_violate_pos, N = can_violate_neg
    //
    //    P N
    //    0 0 => independent
    //    0 1 => positive unate
    //    1 0 => negative unate
    //    1 1 => binate
    // --------------------------------------------------------------
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
        // binate: both violations SAT – also need to print patterns
        printf( "binate\n" );

        int nCisCone = Abc_NtkCiNum( pCone );

        // Pattern 1: from "not positive unate" assignment
        if ( can_violate_pos ) {
            SolveWithAssumps( pSat, assumpsPos );
            for ( int k = 0; k < nCisCone; ++k ) {
                Abc_Obj_t * pCiConeK = Abc_NtkCi( pCone, k );
                if ( Abc_ObjId( pCiConeK ) == idOrig ) {
                    printf( "-" );
                    continue;
                }
                Aig_Obj_t * pAigCiK = (Aig_Obj_t *)pCiConeK->pCopy;
                int varK = pCnfA->pVarNums[ Aig_ObjId( pAigCiK ) ];
                int valK = sat_solver_var_value( pSat, varK );
                printf( valK ? "1" : "0" );
            }
            printf( "\n" );
        }

        // Pattern 2: from "not negative unate" assignment
        if ( can_violate_neg ) {
            SolveWithAssumps( pSat, assumpsNeg );
            for ( int k = 0; k < nCisCone; ++k ) {
                Abc_Obj_t * pCiConeK = Abc_NtkCi( pCone, k );
                if ( Abc_ObjId( pCiConeK ) == idOrig ) {
                    printf( "-" );
                    continue;
                }
                Aig_Obj_t * pAigCiK = (Aig_Obj_t *)pCiConeK->pCopy;
                int varK = pCnfA->pVarNums[ Aig_ObjId( pAigCiK ) ];
                int valK = sat_solver_var_value( pSat, varK );
                printf( valK ? "1" : "0" );
            }
            printf( "\n" );
        }
    }

    // --- 10. Cleanup ---
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
