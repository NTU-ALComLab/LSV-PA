/**
 * @file lsvUnate.cpp
 * @brief BDD Unateness checking (Debug Safe Version)
 */

#include <cstdint>
#include <vector>
#include <cstdio>

// Define pointer types if missing
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

void Lsv_PrintPattern(DdManager * dd, char * cubeVals, int nVars, Abc_Ntk_t * pNtk, int inputIdx) {
    int nInputs = Abc_NtkCiNum(pNtk);
    for (int j = 0; j < nInputs; j++) {
        if (j == inputIdx) {
            printf("-");
            continue;
        }

        Abc_Obj_t * pVarObj = Abc_NtkCi(pNtk, j);
        DdNode * pVar = (DdNode *)pVarObj->pData;
        
        // Safety: If pVar is missing
        if (!pVar) { 
            printf("0"); 
            continue; 
        }

        // Get the index used in the BDD manager
        int bddVarIdx = Cudd_Regular(pVar)->index;
        
        // CRITICAL SAFETY CHECK: Prevent Segfault
        if (bddVarIdx < 0 || bddVarIdx >= nVars) {
            // This variable index is outside the array we allocated!
            // Default to 0 to keep running.
            printf("0"); 
            continue;
        }

        // 0=False, 1=True, 2=DontCare
        int val = (int)cubeVals[bddVarIdx];
        if (val == 1) printf("1");
        else printf("0"); // Treat 0 and DontCare as 0
    }
    printf("\n");
}

// -----------------------------------------------------------------------------
// Main Logic
// -----------------------------------------------------------------------------

void Lsv_NtkUnateBdd(Abc_Ntk_t * pNtk, int outIdx, int inIdx) {
    DdManager * dd = (DdManager *)pNtk->pManFunc;
    if (!dd) { 
        fprintf(stderr, "Error: BDD Manager is NULL. Run 'collapse' first?\n"); 
        return; 
    }

    // 1. Get Input BDD
    Abc_Obj_t * pCi = Abc_NtkCi(pNtk, inIdx);
    DdNode * pVar = (DdNode *)pCi->pData;
    if (!pVar) { 
        fprintf(stderr, "Error: Input %d BDD data is NULL.\n", inIdx); 
        return; 
    }

    // 2. Get Output BDD
    // Note: Abc_ObjGlobalBdd is safe, but let's do manual driver lookup to be sure
    Abc_Obj_t * pCo = Abc_NtkCo(pNtk, outIdx);
    Abc_Obj_t * pDriver = Abc_ObjFanin0(pCo);
    DdNode * pFunc = NULL;

    if (Abc_ObjIsCi(pDriver)) {
        // Output is driven directly by an Input (e.g. y = a)
        pFunc = (DdNode *)pDriver->pData;
    } else if (Abc_ObjIsNode(pDriver)) {
        // Output is driven by a Logic Node
        pFunc = (DdNode *)pDriver->pData;
    } else {
        // Constant or other
        printf("independent\n");
        return;
    }

    // Handle Inverter on Output
    if (Abc_ObjFaninC0(pCo)) {
        pFunc = Cudd_Not(pFunc);
    }
    
    if (!pFunc) { 
        fprintf(stderr, "Error: Output %d BDD is NULL.\n", outIdx); 
        return; 
    }

    // 3. Compute Cofactors
    DdNode * f1 = Cudd_Cofactor(dd, pFunc, pVar);       Cudd_Ref(f1);
    DdNode * f0 = Cudd_Cofactor(dd, pFunc, Cudd_Not(pVar)); Cudd_Ref(f0);

    // 4. Check Relations
    if (f1 == f0) {
        printf("independent\n");
    } 
    else if (Cudd_bddLeq(dd, f0, f1)) {
        printf("positive unate\n");
    } 
    else if (Cudd_bddLeq(dd, f1, f0)) {
        printf("negative unate\n");
    } 
    else {
        printf("binate\n");
        
        // 5. Pattern Generation
        // Get number of variables to size array safely
        int nVars = Cudd_ReadSize(dd);
        if (nVars <= 0) nVars = 1; // Prevention against 0 alloc
        
        // Allocate with vector for automatic cleanup (simpler/safer than new/delete)
        std::vector<char> cubeVals(nVars + 100, 2); // +100 padding for safety

        // Pattern 1: f1=1, f0=0
        DdNode * diff1 = Cudd_bddAnd(dd, f1, Cudd_Not(f0)); Cudd_Ref(diff1);
        if (diff1 != Cudd_ReadLogicZero(dd)) {
             // Pass the raw pointer to CUDD
             if (Cudd_bddPickOneCube(dd, diff1, cubeVals.data())) {
                 Lsv_PrintPattern(dd, cubeVals.data(), nVars, pNtk, inIdx);
             }
        }
        Cudd_RecursiveDeref(dd, diff1);
        
        // Pattern 2: f1=0, f0=1
        DdNode * diff2 = Cudd_bddAnd(dd, Cudd_Not(f1), f0); Cudd_Ref(diff2);
        if (diff2 != Cudd_ReadLogicZero(dd)) {
             if (Cudd_bddPickOneCube(dd, diff2, cubeVals.data())) {
                 Lsv_PrintPattern(dd, cubeVals.data(), nVars, pNtk, inIdx);
             }
        }
        Cudd_RecursiveDeref(dd, diff2);
    }

    Cudd_RecursiveDeref(dd, f1);
    Cudd_RecursiveDeref(dd, f0);
    
    // Force output to appear
    fflush(stdout);
}

int Lsv_CommandUnateBdd(Abc_Frame_t * pAbc, int argc, char ** argv) {
    if (argc != 3) {
        printf("Usage: lsv_unate_bdd <out_index> <in_index>\n");
        return 1;
    }
    
    int outIdx = atoi(argv[1]);
    int inIdx = atoi(argv[2]);
    
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) { 
        printf("Error: Empty network.\n"); 
        return 1; 
    }
    
    if (!Abc_NtkIsBddLogic(pNtk)) { 
        printf("Error: Network not in BDD format. Run 'collapse' first.\n"); 
        return 1; 
    }
    
    // Bounds check
    if (outIdx < 0 || outIdx >= Abc_NtkCoNum(pNtk)) return 1;
    if (inIdx < 0 || inIdx >= Abc_NtkCiNum(pNtk)) return 1;
    
    Lsv_NtkUnateBdd(pNtk, outIdx, inIdx);
    return 0;
}
