// src/ext-lsv/lsvUnateSat.cpp
//
// SAT-based unateness checking for PA2 Problem 2.
//
// Usage in ABC:
//   lsv_unate_sat <k> <i>
//   k = PO index (0-based)
//   i = PI index (0-based)
//
// Output:
//   positive unate
//   negative unate
//   independent
// or
//   binate
//   <pattern 1>
//   <pattern 2>
//
// This file self-registers the command using Abc_FrameInitializer_t,
// so you do NOT need to modify lsvCmd.cpp.

#include <vector>
#include <string>

extern "C" {
#include "base/abc/abc.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"

// From PA2 hint (not in any header)
Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

// =====================================================================
// Helper functions
// =====================================================================

// sign = 0 → positive literal, sign = 1 → negative literal.
static inline lit mkLitVar( int v, int sign )
{
    lit l = toLit( v );
    return sign ? lit_neg( l ) : l;
}

// sat_solver_solve wrapper with no limits.
static inline int SatSolveWithAssumps(
    sat_solver * pSat,
    lit * pBeg,
    lit * pEnd
)
{
    return sat_solver_solve( pSat, pBeg, pEnd, 0, 0, 0, 0 );
}

// Add vA == vB: (¬vA ∨ vB) ∧ (vA ∨ ¬vB).
static inline void AddEquality( sat_solver * pSat, int vA, int vB )
{
    lit clause[2];

    clause[0] = mkLitVar( vA, 1 );
    clause[1] = mkLitVar( vB, 0 );
    sat_solver_addclause( pSat, clause, clause + 2 );

    clause[0] = mkLitVar( vA, 0 );
    clause[1] = mkLitVar( vB, 1 );
    sat_solver_addclause( pSat, clause, clause + 2 );
}

// Build pattern string from SAT model (copy A) with '-' at iPi.
static std::string BuildPattern(
    const std::vector<int> & vPiVarA,
    int iPi,
    int nPi,
    sat_solver * pSat
)
{
    std::string s;
    s.reserve( nPi );
    for ( int t = 0; t < nPi; ++t )
    {
        if ( t == iPi )
        {
            s.push_back( '-' );
            continue;
        }

        int vA = vPiVarA[t];
        if ( vA < 0 )
        {
            // PI not in cone / not encoded → don't-care, choose 0
            s.push_back( '0' );
        }
        else
        {
            int val = sat_solver_var_value( pSat, vA );
            s.push_back( val ? '1' : '0' );
        }
    }
    return s;
}

// =====================================================================
// Core unateness checker
// =====================================================================

static void Lsv_NtkUnateSatCore( Abc_Ntk_t * pNtk, int iPo, int iPi )
{
    if ( !Abc_NtkIsStrash( pNtk ) )
    {
        Abc_Print( 1, "Please run \"strash\" before lsv_unate_sat.\n" );
        return;
    }

    if ( iPo < 0 || iPo >= Abc_NtkPoNum( pNtk ) )
    {
        Abc_Print( 1, "PO index %d out of range (0..%d).\n",
                   iPo, Abc_NtkPoNum( pNtk ) - 1 );
        return;
    }

    if ( iPi < 0 || iPi >= Abc_NtkPiNum( pNtk ) )
    {
        Abc_Print( 1, "PI index %d out of range (0..%d).\n",
                   iPi, Abc_NtkPiNum( pNtk ) - 1 );
        return;
    }

    Abc_Obj_t * pPo    = Abc_NtkPo( pNtk, iPo );
    Abc_Obj_t * pFanin = Abc_ObjFanin0( pPo );
    int         fComplOrig = Abc_ObjFaninC0( pPo ); // 1 if PO is ~fanin

    // -------------------------------------------------------------
    // 1. Build cone rooted at the FANIN of the PO
    //    (Abc_NtkCreateCone cannot take a CO as root).
    // -------------------------------------------------------------
    Abc_Ntk_t * pCone =
        Abc_NtkCreateCone( pNtk, pFanin, Abc_ObjName( pPo ), 1 );
    if ( pCone == NULL )
    {
        Abc_Print( 1, "Abc_NtkCreateCone failed.\n" );
        return;
    }

    // -------------------------------------------------------------
    // 2. Convert cone to AIG and derive CNF for copy A
    // -------------------------------------------------------------
    Aig_Man_t * pAig = Abc_NtkToDar( pCone, 0, 0 );
    if ( pAig == NULL )
    {
        Abc_Print( 1, "Abc_NtkToDar failed.\n" );
        Abc_NtkDelete( pCone );
        return;
    }

    Cnf_Dat_t * pCnfA = Cnf_Derive( pAig, 1 );
    if ( pCnfA == NULL )
    {
        Abc_Print( 1, "Cnf_Derive failed.\n" );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // -------------------------------------------------------------
    // 3. SAT solver: CNF for copy A and lifted copy B
    // -------------------------------------------------------------
    sat_solver * pSat = sat_solver_new();
    if ( pSat == NULL )
    {
        Abc_Print( 1, "sat_solver_new failed.\n" );
        Cnf_DataFree( pCnfA );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // Copy A: vars [0 .. nVarsA-1]
    Cnf_DataWriteIntoSolverInt( pSat, pCnfA, 1, 0 );
    int nVarsA = pCnfA->nVars;

    // Copy B: vars [nVarsA .. 2*nVarsA-1]
    Cnf_DataLift( pCnfA, nVarsA );
    Cnf_DataWriteIntoSolverInt( pSat, pCnfA, 1, 0 );
    Cnf_DataLift( pCnfA, -nVarsA ); // restore

    // -------------------------------------------------------------
    // 4. Map original PIs → cone PIs → CNF vars (copy A/B)
    // -------------------------------------------------------------
    int nPi = Abc_NtkPiNum( pNtk );
    std::vector<int> vPiVarA( nPi, -1 );
    std::vector<int> vPiVarB( nPi, -1 );

    for ( int t = 0; t < nPi; ++t )
    {
        Abc_Obj_t * pPiOrig = Abc_NtkPi( pNtk, t );
        Abc_Obj_t * pPiCone = Abc_NtkObj( pCone, Abc_ObjId( pPiOrig ) );
        if ( pPiCone == NULL )
            continue; // PI not in cone

        int vA = pCnfA->pVarNums[ pPiCone->Id ];
        if ( vA < 0 )
            continue; // not encoded in CNF

        vPiVarA[t] = vA;
        vPiVarB[t] = vA + nVarsA;
    }

    int varX_A = vPiVarA[iPi];
    int varX_B = vPiVarB[iPi];

    if ( varX_A < 0 || varX_B < 0 )
    {
        // Abc_Print( 1, "[DEBUG] x%d not in cone of y%d → independent.\n",
        //            iPi, iPo );
        Abc_Print( 1, "independent\n" );
        sat_solver_delete( pSat );
        Cnf_DataFree( pCnfA );
        Aig_ManStop( pAig );
        Abc_NtkDelete( pCone );
        return;
    }

    // -------------------------------------------------------------
    // 5. Equality constraints vA(t) == vB(t) for all t ≠ iPi
    // -------------------------------------------------------------
    for ( int t = 0; t < nPi; ++t )
    {
        if ( t == iPi )
            continue;
        int vA = vPiVarA[t];
        int vB = vPiVarB[t];
        if ( vA < 0 || vB < 0 )
            continue;
        AddEquality( pSat, vA, vB );
    }

    // -------------------------------------------------------------
    // 6. Output literal y in both copies
    //
    // In the cone AIG, CO 0 is the *fanin* function (no extra PO
    // inversion). The real PO of the original network is:
    //
    //   y = (fCone) ^ fComplOrig
    //
    // so we must apply fComplOrig when converting the root var to
    // a SAT literal.
    // -------------------------------------------------------------
    Aig_Obj_t * pCo   = Aig_ManCo( pAig, 0 );
    Aig_Obj_t * pRoot = Aig_ObjFanin0( pCo );
    int varRootA      = pCnfA->pVarNums[ pRoot->Id ];
    int varRootB      = varRootA + nVarsA;

    lit litY_A = mkLitVar( varRootA, fComplOrig );
    lit litY_B = mkLitVar( varRootB, fComplOrig );

    // Abc_Print( 1,
    //     "[DEBUG] y%d in x%d: rootA=%d rootB=%d fComplOrig=%d "
    //     "varX_A=%d varX_B=%d\n",
    //     iPo, iPi, varRootA, varRootB, fComplOrig, varX_A, varX_B );

    // -------------------------------------------------------------
    // 7. SAT queries for two types of counterexamples
    // -------------------------------------------------------------
    bool hasPosCE = false; // CE where y goes 1→0 (violates positive-unate)
    bool hasNegCE = false; // CE where y goes 0→1 (violates negative-unate)
    std::string patPos, patNeg;
    lit assumps[4];

    // --------- (a) CE to positive-unateness ----------
    // Need assignment:
    //   x_i^A = 0, x_i^B = 1,
    //   y^A   = 1, y^B   = 0.
    assumps[0] = mkLitVar( varX_A, 1 ); // xi^A = 0
    assumps[1] = mkLitVar( varX_B, 0 ); // xi^B = 1
    assumps[2] = litY_A;                // y^A  = 1
    assumps[3] = lit_neg( litY_B );     // y^B  = 0

    int status = SatSolveWithAssumps( pSat, assumps, assumps + 4 );
    if ( status == l_True )
    {
        hasPosCE = true;
        patPos   = BuildPattern( vPiVarA, iPi, nPi, pSat );

        int xA = sat_solver_var_value( pSat, varX_A );
        int xB = sat_solver_var_value( pSat, varX_B );
        int rA = sat_solver_var_value( pSat, varRootA );
        int rB = sat_solver_var_value( pSat, varRootB );
        int yA = rA ^ fComplOrig;
        int yB = rB ^ fComplOrig;

        // Abc_Print( 1,
        //     "[DEBUG] CE-positive SAT: xA=%d xB=%d rootA=%d rootB=%d "
        //     "→ yA=%d yB=%d pattern=%s\n",
        //     xA, xB, rA, rB, yA, yB, patPos.c_str() );
    }
    else
    {
        // Abc_Print( 1, "[DEBUG] CE-positive UNSAT.\n" );
    }

    // --------- (b) CE to negative-unateness ----------
    // Need assignment:
    //   x_i^A = 0, x_i^B = 1,
    //   y^A   = 0, y^B   = 1.
    assumps[0] = mkLitVar( varX_A, 1 ); // xi^A = 0
    assumps[1] = mkLitVar( varX_B, 0 ); // xi^B = 1
    assumps[2] = lit_neg( litY_A );     // y^A  = 0
    assumps[3] = litY_B;                // y^B  = 1

    status = SatSolveWithAssumps( pSat, assumps, assumps + 4 );
    if ( status == l_True )
    {
        hasNegCE = true;
        patNeg   = BuildPattern( vPiVarA, iPi, nPi, pSat );

        int xA = sat_solver_var_value( pSat, varX_A );
        int xB = sat_solver_var_value( pSat, varX_B );
        int rA = sat_solver_var_value( pSat, varRootA );
        int rB = sat_solver_var_value( pSat, varRootB );
        int yA = rA ^ fComplOrig;
        int yB = rB ^ fComplOrig;

            // Abc_Print( 1,
            //     "[DEBUG] CE-negative SAT: xA=%d xB=%d rootA=%d rootB=%d "
            //     "→ yA=%d yB=%d pattern=%s\n",
            //     xA, xB, rA, rB, yA, yB, patNeg.c_str() );
    }
    else
    {
        // Abc_Print( 1, "[DEBUG] CE-negative UNSAT.\n" );
    }

    // Abc_Print( 1,
    //     "[DEBUG] Summary y%d in x%d: hasPosCE=%d hasNegCE=%d\n",
    //     iPo, iPi, hasPosCE, hasNegCE );

    // -------------------------------------------------------------
    // 8. Final classification
    // -------------------------------------------------------------
    if ( hasPosCE && hasNegCE )
    {
        Abc_Print( 1, "binate\n" );
        Abc_Print( 1, "%s\n", patPos.c_str() );
        Abc_Print( 1, "%s\n", patNeg.c_str() );
    }
    else if ( hasPosCE && !hasNegCE )
    {
        // We can have y drop (1→0) when x increases, but never rise (0→1).
        Abc_Print( 1, "negative unate\n" );
    }
    else if ( !hasPosCE && hasNegCE )
    {
        // We can have y rise (0→1) when x increases, but never drop (1→0).
        Abc_Print( 1, "positive unate\n" );
    }
    else
    {
        // No change in y when x flips.
        Abc_Print( 1, "independent\n" );
    }

    // -------------------------------------------------------------
    // 9. Cleanup
    // -------------------------------------------------------------
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnfA );
    Aig_ManStop( pAig );
    Abc_NtkDelete( pCone );
}

// =====================================================================
// ABC command wrapper
// =====================================================================

int Lsv_CommandUnateSAT( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk( pAbc );
    if ( pNtk == NULL )
    {
        Abc_Print( 1, "Empty network.\n" );
        return 1;
    }

    // argv[0] = "lsv_unate_sat"
    // argv[1] = k
    // argv[2] = i
    if ( argc != 3 )
    {
        Abc_Print( 1, "usage: lsv_unate_sat <k> <i>\n" );
        return 1;
    }

    int iPo = atoi( argv[1] );
    int iPi = atoi( argv[2] );
    Lsv_NtkUnateSatCore( pNtk, iPo, iPi );
    return 0;
}

// =====================================================================
// Registration into ABC (per-command initializer)
// =====================================================================

static void init_unatesat( Abc_Frame_t * pAbc )
{
    // Abc_Print( 1, "[lsv_unate_sat] registering command.\n" );
    Cmd_CommandAdd( pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSAT, 0 );
}

static void destroy_unatesat( Abc_Frame_t * /*pAbc*/ )
{
    // nothing to clean up
}

static Abc_FrameInitializer_t frame_initializer_unatesat =
{
    init_unatesat,
    destroy_unatesat
};

struct UnateSATRegistrationManager
{
    UnateSATRegistrationManager()
    {
        Abc_FrameAddInitializer( &frame_initializer_unatesat );
    }
};

static UnateSATRegistrationManager s_UnateSATRegistrationManager;
