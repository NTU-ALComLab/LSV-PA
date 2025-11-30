/**
 * @file lsvUnateSat.cpp
 * @brief SAT-based unateness checking for PA2 (Part 2)
 *
 * Command (from lsvCmd.cpp):
 *     lsv_unate_sat <po_idx> <pi_idx>
 *
 * Assumes:
 *   - The current network has been strashed: use "strash" before calling.
 */

#include <vector>
#include <cstdio>
#include <cassert>

extern "C" {
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
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

    // Map POs and PIs
    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, poIdx);
    Abc_Obj_t* pPi = Abc_NtkPi(pNtk, piIdx);

    // Convert the *whole* strashed network to an AIG
    Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
    if (!pAig) {
        Abc_Print(-1, "Error: Abc_NtkToDar() failed.\n");
        return;
    }

    // Derive CNF for AIG
    Cnf_Dat_t* pCnf = Cnf_Derive(pAig, 1);
    if (!pCnf) {
        Abc_Print(-1, "Error: Cnf_Derive() failed.\n");
        Aig_ManStop(pAig);
        return;
    }

    // SAT solver with 2 copies of the CNF: copy A and copy B
    int nVars   = pCnf->nVars;
    int nCla    = pCnf->nClauses;
    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars(pSat, 2 * nVars);

    // Feed CNF for copy A and copy B (B is lifted by nVars)
    Cnf_DataLift(pCnf, 0);        // copy A: offset 0
    Cnf_DataWriteIntoSolver(pSat, pCnf, 1, 0);

    Cnf_DataLift(pCnf, nVars);    // copy B: offset nVars
    Cnf_DataWriteIntoSolver(pSat, pCnf, 1, 0);

    // Undo lift so that pCnf->pVarNums stays "canonical"
    Cnf_DataLift(pCnf, -nVars);

    // === Map output and input to CNF variable indices ===

    // Output: PO's fanin in AIG
    Aig_Obj_t* pAigPo  = (Aig_Obj_t*)pPo->pCopy;       // CO object
    Aig_Obj_t* pLitOut = Aig_ObjChild0(pAigPo);        // literal for function
    int fOutCompl      = Aig_IsComplement(pLitOut);    // 1 if complemented
    Aig_Obj_t* pOutReg = Aig_Regular(pLitOut);

    int varY = pCnf->pVarNums[Aig_ObjId(pOutReg)];
    int varYA = varY;           // copy A
    int varYB = varY + nVars;   // copy B

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

    // === Helper for SAT calls ===
    auto SolveWithAssumps = [&](const std::vector<lit>& assumps) -> bool {
        // returns true iff SAT
        int status = sat_solver_solve(
            pSat,
            const_cast<lit*>(assumps.data()),
            const_cast<lit*>(assumps.data()) + assumps.size(),
            0, 0, 0, 0
        );
        // In ABC, 1 = SAT, 0 = UNSAT, -1 = timeout
        return (status == 1);
    };

    // === Build assumptions for "not positive unate" ===
    // "not positive" means ∃ X: y(0, Z) = 1 and y(1, Z) = 0
    //
    // y^A = 1, y^B = 0
    // taking into account output complement:
    // if fOutCompl = 0 => y-literal is (varY, 0) for 1, (varY,1) for 0
    // if fOutCompl = 1 => y-literal is (varY,1) for 1, (varY,0) for 0

    int polY1A = fOutCompl ? 1 : 0;   // polarity to make y = 1
    int polY0A = fOutCompl ? 0 : 1;   // polarity to make y = 0

    std::vector<lit> assumpsNotPos;
    assumpsNotPos.reserve(4);

    // y^A = 1
    assumpsNotPos.push_back( Abc_Var2Lit(varYA, polY1A) );
    // y^B = 0
    assumpsNotPos.push_back( Abc_Var2Lit(varYB, polY0A) );
    // x^A = 0, x^B = 1 (no complement on CI itself)
    assumpsNotPos.push_back( Abc_Var2Lit(varXA, 1) );
    assumpsNotPos.push_back( Abc_Var2Lit(varXB, 0) );

    bool canViolatePos = SolveWithAssumps(assumpsNotPos);

    // === Build assumptions for "not negative unate" ===
    // "not negative" means ∃ X: y(0, Z) = 0 and y(1, Z) = 1
    std::vector<lit> assumpsNotNeg;
    assumpsNotNeg.reserve(4);

    // y^A = 0, y^B = 1
    assumpsNotNeg.push_back( Abc_Var2Lit(varYA, polY0A) );
    assumpsNotNeg.push_back( Abc_Var2Lit(varYB, polY1A) );
    // x^A = 0, x^B = 1 flipped? (no, still 0/1, but we swap which copy interprets them)
    // For y(0,Z)=0 and y(1,Z)=1 we keep the same "0 in A, 1 in B" convention.
    assumpsNotNeg.push_back( Abc_Var2Lit(varXA, 1) );
    assumpsNotNeg.push_back( Abc_Var2Lit(varXB, 0) );

    bool canViolateNeg = SolveWithAssumps(assumpsNotNeg);

    // Interpret result
    PrintUnateResult(canViolatePos, canViolateNeg);

    // Clean up
    Cnf_DataFree(pCnf);
    Aig_ManStop(pAig);
    sat_solver_delete(pSat);
}
