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

// cubeVals: length = Cudd_ReadSize(dd), cubeVals[v] in {0,1,2} for BDD var index v
// We must map each primary input x_j to its BDD var index via pCi->pData.
void Lsv_PrintPattern(DdManager * dd,
                      char * cubeVals,
                      int nVars,
                      Abc_Ntk_t * pNtk,
                      int inputIdx)
{
    int nInputs = Abc_NtkCiNum(pNtk);

    for (int j = 0; j < nInputs; ++j) {
        // The tested input x_i is always printed as '-'
        if (j == inputIdx) {
            printf("-");
            continue;
        }

        // Map CI j to its BDD variable index
        Abc_Obj_t * pCi = Abc_NtkCi(pNtk, j);
        DdNode    * pVarCi = (DdNode *)pCi->pData;

        if (!pVarCi) {
            // If something is wrong, fall back to 0
            printf("0");
            continue;
        }

        int varIdx = Cudd_NodeReadIndex(pVarCi); // BDD variable index in CUDD

        if (varIdx < 0 || varIdx >= nVars) {
            printf("0");
            continue;
        }

        char v = cubeVals[varIdx];
        // cubeVals entries: 0 (False), 1 (True), 2 (Don't Care)
        // For printing, Don't Care is treated as 0.
        if (v == 1)
            printf("1");
        else
            printf("0");
    }
    printf("\n");
}

// -----------------------------------------------------------------------------
// Main Logic
// -----------------------------------------------------------------------------

void Lsv_NtkUnateBdd(Abc_Ntk_t * pNtk, int outIdx, int inIdx)
{
    // 1. Get BDD Manager
    DdManager * dd = (DdManager *)pNtk->pManFunc;
    if (!dd) {
        printf("Error: BDD Manager is NULL. Run 'collapse' first.\n");
        return;
    }

    // 2. Get the BDD variable for input x_i from its CI node
    Abc_Obj_t * pCi = Abc_NtkCi(pNtk, inIdx);
    DdNode    * pVar = (DdNode *)pCi->pData;
    if (!pVar) {
        printf("Error: CI %d has no BDD variable (pData is NULL).\n", inIdx);
        return;
    }

    // We temporarily increase its ref count while we use it
    Cudd_Ref(pVar);

    // 3. Get Output BDD function from its driver node (local BDD)
    Abc_Obj_t * pCo     = Abc_NtkCo(pNtk, outIdx);
    Abc_Obj_t * pDriver = Abc_ObjFanin0(pCo);
    DdNode    * pFunc   = (DdNode *)pDriver->pData;

    if (!pFunc) {
        printf("Error: Output BDD is NULL (driver has no local BDD).\n");
        Cudd_RecursiveDeref(dd, pVar);
        return;
    }

    // 4. Compute cofactors f1 = f|_{x_i=1}, f0 = f|_{x_i=0}
    DdNode * f1 = Cudd_Cofactor(dd, pFunc, pVar);           Cudd_Ref(f1);
    DdNode * f0 = Cudd_Cofactor(dd, pFunc, Cudd_Not(pVar)); Cudd_Ref(f0);

    // 5. Classify unateness
    if (f1 == f0) {
        printf("independent\n");
    }
    else if (Cudd_bddLeq(dd, f0, f1)) {
        // f0 <= f1  ⇒ monotone increasing in x_i ⇒ positive unate
        printf("positive unate\n");
    }
    else if (Cudd_bddLeq(dd, f1, f0)) {
        // f1 <= f0  ⇒ monotone decreasing in x_i ⇒ negative unate
        printf("negative unate\n");
    }
    else {
        printf("binate\n");

        // 6. Generate patterns for binate case
        int nVars = Cudd_ReadSize(dd);
        std::vector<char> cubeVals(nVars, 2);

        // Pattern 1: cube in (f1 & !f0) ⇒ cofactor equals x_i
        DdNode * diff1 = Cudd_bddAnd(dd, f1, Cudd_Not(f0)); Cudd_Ref(diff1);
        if (diff1 != Cudd_ReadLogicZero(dd)) {
            if (Cudd_bddPickOneCube(dd, diff1, cubeVals.data())) {
                Lsv_PrintPattern(dd, cubeVals.data(), nVars, pNtk, inIdx);
            }
        }
        Cudd_RecursiveDeref(dd, diff1);

        // Pattern 2: cube in (!f1 & f0) ⇒ cofactor equals ¬x_i
        DdNode * diff2 = Cudd_bddAnd(dd, Cudd_Not(f1), f0); Cudd_Ref(diff2);
        if (diff2 != Cudd_ReadLogicZero(dd)) {
            if (Cudd_bddPickOneCube(dd, diff2, cubeVals.data())) {
                Lsv_PrintPattern(dd, cubeVals.data(), nVars, pNtk, inIdx);
            }
        }
        Cudd_RecursiveDeref(dd, diff2);
    }

    // Cleanup
    Cudd_RecursiveDeref(dd, f1);
    Cudd_RecursiveDeref(dd, f0);
    Cudd_RecursiveDeref(dd, pVar);

    fflush(stdout);
}

// -----------------------------------------------------------------------------
// ABC Command Wrapper
// -----------------------------------------------------------------------------

int Lsv_CommandUnateBdd(Abc_Frame_t * pAbc, int argc, char ** argv)
{
    if (argc != 3) {
        printf("Usage: lsv_unate_bdd <out_index> <in_index>\n");
        return 1;
    }

    int outIdx = atoi(argv[1]);
    int inIdx  = atoi(argv[2]);

    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        printf("Error: Empty network.\n");
        return 1;
    }

    if (!Abc_NtkIsBddLogic(pNtk)) {
        printf("Error: Network not in BDD format. Run 'collapse' first.\n");
        return 1;
    }

    if (outIdx < 0 || outIdx >= Abc_NtkCoNum(pNtk)) {
        printf("Error: Invalid output index %d.\n", outIdx);
        return 1;
    }
    if (inIdx < 0 || inIdx >= Abc_NtkCiNum(pNtk)) {
        printf("Error: Invalid input index %d.\n", inIdx);
        return 1;
    }

    Lsv_NtkUnateBdd(pNtk, outIdx, inIdx);
    return 0;
}
