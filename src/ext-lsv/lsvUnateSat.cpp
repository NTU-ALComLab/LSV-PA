/**
 * @file lsvUnateSat.cpp
 * @brief SAT-based unateness checking for PA2 (Part 2)
 *
 * Command: lsv_unate_sat <po_idx> <pi_idx>
 */

#include <vector>
#include <cstdio>
#include <cassert>

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

////////////////////////////////////////////////////////////////////////
/// Helpers
////////////////////////////////////////////////////////////////////////

// Add equality constraint xA == xB
static void AddEquality(sat_solver* pSat, int vA, int vB)
{
    // (¬xA ∨  xB)
    // ( xA ∨ ¬xB)
    lit lits[2];

    lits[0] = Abc_Var2Lit(vA, 1);
    lits[1] = Abc_Var2Lit(vB, 0);
    sat_solver_addclause(pSat, lits, lits+2);

    lits[0] = Abc_Var2Lit(vA, 0);
    lits[1] = Abc_Var2Lit(vB, 1);
    sat_solver_addclause(pSat, lits, lits+2);
}

// Pretty print the final result given flags
static void PrintUnateResult(bool canPos, bool canNeg)
{
    if (!canPos && !canNeg)
        Abc_Print(1, "independent\n");
    else if (!canPos &&  canNeg)
        Abc_Print(1, "positive unate\n");
    else if ( canPos && !canNeg)
        Abc_Print(1, "negative unate\n");
    else
        Abc_Print(1, "binate\n");
}

////////////////////////////////////////////////////////////////////////
/// Core procedure (works on the whole strashed network)
////////////////////////////////////////////////////////////////////////

static void Lsv_NtkUnateSatCore(Abc_Ntk_t* pNtk, int poIdx, int piIdx)
{
    // Basic sanity checks on ABC side
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "Error: network is not strashed. Use \"strash\" first.\n");
        return;
    }
    if (poIdx < 0 || poIdx >= Abc_NtkPoNum(pNtk)) {
        Abc_Print(-1, "Error: PO index %d out of range.\n", poIdx);
        return;
    }
    if (piIdx < 0 || piIdx >= Abc_NtkPiNum(pNtk)) {
        Abc_Print(-1, "Error: PI index %d out of range.\n", piIdx);
        return;
    }

    // Convert the *whole* strashed network to an AIG
    Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
    if (!pAig) {
        Abc_Print(-1, "Error: Abc_NtkToDar() failed.\n");
        return;
    }

    // Sanity: AIG CI/CO counts should match ABC PI/PO counts
    if ( Aig_ManCiNum(pAig) != Abc_NtkPiNum(pNtk) ||
         Aig_ManCoNum(pAig) != Abc_NtkPoNum(pNtk) ) {
        Abc_Print(-1, "Error: mismatch between network PIs/POs and AIG CIs/COs.\n");
        Aig_ManStop(pAig);
        return;
    }

    // Derive CNF for this AIG
    Cnf_Dat_t* pCnf = Cnf_Derive(pAig, 1);
    if (!pCnf) {
        Abc_Print(-1, "Error: Cnf_Derive() failed.\n");
        Aig_ManStop(pAig);
        return;
    }

    int nVars = pCnf->nVars;

    // SAT solver
    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars(pSat, 2 * nVars);

    // Copy A: CNF as-is
    Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);

    // Copy B: lift by nVars and feed again
    Cnf_DataLift(pCnf, nVars);
    Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);

    // Restore pCnf->pVarNums to original (optional but nice)
    Cnf_DataLift(pCnf, -nVars);

    // === Map output and input to CNF variable indices ===
    // Use AIG CI/CO order directly; no pCopy dependence.

    // Output: poIdx-th CO in AIG
    Aig_Obj_t* pAigCo    = Aig_ManCo(pAig, poIdx);
    Aig_Obj_t* pLitOut   = Aig_ObjChild0(pAigCo);        // literal for function
    int        fOutCompl = Aig_IsComplement(pLitOut);    // 1 if complemented at PO
    Aig_Obj_t* pOutReg   = Aig_Regular(pLitOut);

    int varY  = pCnf->pVarNums[Aig_ObjId(pOutReg)];
    int varYA = varY;            // copy A
    int varYB = varY + nVars;    // copy B

    // Input: piIdx-th CI in AIG
    Aig_Obj_t* pAigCi = Aig_ManCi(pAig, piIdx);
    Aig_Obj_t* pCiReg = Aig_Regular(pAigCi);
    int varX  = pCnf->pVarNums[Aig_ObjId(pCiReg)];
    int varXA = varX;
    int varXB = varX + nVars;

    // === Add equalities for all other PIs (CIs) ===
    int nCi = Aig_ManCiNum(pAig);
    for (int i = 0; i < nCi; ++i) {
        if (i == piIdx) continue;   // skip tested PI

        Aig_Obj_t* pCi2    = Aig_ManCi(pAig, i);
        Aig_Obj_t* pCi2Reg = Aig_Regular(pCi2);
        int varZ  = pCnf->pVarNums[Aig_ObjId(pCi2Reg)];
        int varZA = varZ;
        int varZB = varZ + nVars;
        AddEquality(pSat, varZA, varZB);
    }

    // Helper: run SAT and interpret return as SAT/UNSAT
    auto SolveSAT = [&](const std::vector<lit>& assumps) -> bool {
        int status = sat_solver_solve(
            pSat,
            const_cast<lit*>(assumps.data()),
            const_cast<lit*>(assumps.data()) + assumps.size(),
            0, 0, 0, 0
        );
        // ABC uses l_True / l_False / l_Undef
        return (status == l_True);
    };

    // === Build assumptions for "not positive unate" ===
    // not positive: ∃Z with xA=0, xB=1 and y(0,Z)=1, y(1,Z)=0
    //
    // Our CNF variable is for the regular node F, with:
    //    y = F XOR fOutCompl
    // To enforce y=1 => F = 1 XOR fOutCompl
    //            y=0 => F = 0 XOR fOutCompl

    int polY1 = fOutCompl ? 1 : 0;  // literal polarity making y = 1
    int polY0 = fOutCompl ? 0 : 1;  // literal polarity making y = 0

    std::vector<lit> assumpsNotPos;
    assumpsNotPos.reserve(4);
    assumpsNotPos.push_back( Abc_Var2Lit(varYA, polY1) ); // yA = 1
    assumpsNotPos.push_back( Abc_Var2Lit(varYB, polY0) ); // yB = 0
    assumpsNotPos.push_back( Abc_Var2Lit(varXA, 1) );     // xA = 0
    assumpsNotPos.push_back( Abc_Var2Lit(varXB, 0) );     // xB = 1

    bool canViolatePos = SolveSAT(assumpsNotPos);

    // === Build assumptions for "not negative unate" ===
    // not negative: ∃Z with xA=0, xB=1 and y(0,Z)=0, y(1,Z)=1
    std::vector<lit> assumpsNotNeg;
    assumpsNotNeg.reserve(4);
    assumpsNotNeg.push_back( Abc_Var2Lit(varYA, polY0) ); // yA = 0
    assumpsNotNeg.push_back( Abc_Var2Lit(varYB, polY1) ); // yB = 1
    assumpsNotNeg.push_back( Abc_Var2Lit(varXA, 1) );     // xA = 0
    assumpsNotNeg.push_back( Abc_Var2Lit(varXB, 0) );     // xB = 1

    bool canViolateNeg = SolveSAT(assumpsNotNeg);

    // Print classification first
    PrintUnateResult(canViolatePos, canViolateNeg);

    // === If binate, also print two counterexample patterns (like Exercise 1) ===
    if ( canViolatePos && canViolateNeg )
    {
        // Pattern 1: from a model of "not positive unate"
        if ( SolveSAT(assumpsNotPos) ) {
            for (int i = 0; i < nCi; ++i) {
                if (i == piIdx) {
                    // tested input gets '-'
                    printf("-");
                    continue;
                }
                Aig_Obj_t* pCi2    = Aig_ManCi(pAig, i);
                Aig_Obj_t* pCi2Reg = Aig_Regular(pCi2);
                int varZ  = pCnf->pVarNums[Aig_ObjId(pCi2Reg)];
                int varZA = varZ; // copy A
                int val   = sat_solver_var_value(pSat, varZA); // 0/1
                printf("%d", val ? 1 : 0);
            }
            printf("\n");
        }

        // Pattern 2: from a model of "not negative unate"
        if ( SolveSAT(assumpsNotNeg) ) {
            for (int i = 0; i < nCi; ++i) {
                if (i == piIdx) {
                    printf("-");
                    continue;
                }
                Aig_Obj_t* pCi2    = Aig_ManCi(pAig, i);
                Aig_Obj_t* pCi2Reg = Aig_Regular(pCi2);
                int varZ  = pCnf->pVarNums[Aig_ObjId(pCi2Reg)];
                int varZA = varZ; // copy A
                int val   = sat_solver_var_value(pSat, varZA);
                printf("%d", val ? 1 : 0);
            }
            printf("\n");
        }
    }

    // Clean up
    Cnf_DataFree(pCnf);
    Aig_ManStop(pAig);
    sat_solver_delete(pSat);
}

////////////////////////////////////////////////////////////////////////
/// ABC command wrapper
////////////////////////////////////////////////////////////////////////

int Lsv_CommandUnateSat( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    if ( argc != 3 ) {
        Abc_Print( -1, "Usage: lsv_unate_sat <po_index> <pi_index>\n" );
        return 1;
    }

    int poIdx = atoi( argv[1] );
    int piIdx = atoi( argv[2] );

    Abc_Ntk_t * pNtk = Abc_FrameReadNtk( pAbc );
    if ( !pNtk ) {
        Abc_Print( -1, "Error: empty network.\n" );
        return 1;
    }

    Lsv_NtkUnateSatCore( pNtk, poIdx, piIdx );
    return 0;
}
