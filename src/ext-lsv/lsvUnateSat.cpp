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
/// Core procedure
////////////////////////////////////////////////////////////////////////

void Lsv_NtkUnateSat(Abc_Ntk_t* pNtk, int poIdx, int piIdx)
{
    // Basic sanity checks
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

    // Map POs and PIs in the ABC network
    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, poIdx);
    Abc_Obj_t* pPi = Abc_NtkPi(pNtk, piIdx);

    // Convert the *whole* strashed network to an AIG
    Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
    if (!pAig) {
        Abc_Print(-1, "Error: Abc_NtkToDar() failed.\n");
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

    // Output: PO's fanin in AIG
    Aig_Obj_t* pAigPo  = (Aig_Obj_t*)pPo->pCopy;       // CO object
    Aig_Obj_t* pLitOut = Aig_ObjChild0(pAigPo);        // literal for function
    int fOutCompl      = Aig_IsComplement(pLitOut);    // 1 if complemented at PO
    Aig_Obj_t* pOutReg = Aig_Regular(pLitOut);

    int varY = pCnf->pVarNums[Aig_ObjId(pOutReg)];
    int varYA = varY;            // copy A
    int varYB = varY + nVars;    // copy B

    // Input: PI in AIG
    Aig_Obj_t* pAigPi = (Aig_Obj_t*)pPi->pCopy;        // CI object (not complemented)
    Aig_Obj_t* pPiReg = Aig_Regular(pAigPi);
    int varX = pCnf->pVarNums[Aig_ObjId(pPiReg)];
    int varXA = varX;
    int varXB = varX + nVars;

    // === Add equalities for all other PIs ===
    int nPi = Abc_NtkPiNum(pNtk);
    for (int i = 0; i < nPi; ++i) {
        if (i == piIdx) continue;   // skip tested PI

        Abc_Obj_t* pThisPi = Abc_NtkPi(pNtk, i);
        Aig_Obj_t* pAigPi2 = (Aig_Obj_t*)pThisPi->pCopy;
        Aig_Obj_t* pPi2Reg = Aig_Regular(pAigPi2);
        int varZ = pCnf->pVarNums[Aig_ObjId(pPi2Reg)];

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
        // ABC uses l_True / l_False:
        //   l_True  =  1  (SAT)
        //   l_False =  0  (UNSAT)
        //   l_Undef = -1
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

    // Print classification (no patterns for now — PA2 usually only checks type)
    PrintUnateResult(canViolatePos, canViolateNeg);

    // Clean up
    Cnf_DataFree(pCnf);
    Aig_ManStop(pAig);
    sat_solver_delete(pSat);
}
