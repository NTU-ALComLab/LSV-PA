/**
 * @file lsvUnate.cpp
 * @brief BDD Unateness checking with Debug Prints
 */

#include <cstdint>
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

void Lsv_PrintPattern(DdManager * dd, char * cubeVals, Abc_Ntk_t * pNtk, int inputIdx) {
    int nInputs = Abc_NtkCiNum(pNtk);
    for (int j = 0; j < nInputs; j++) {
        if (j == inputIdx) {
            printf("-");
            continue;
        }

        Abc_Obj_t * pVarObj = Abc_NtkCi(pNtk, j);
        DdNode * pVar = (DdNode *)pVarObj->pData;
        
        // Safety: If pVar is missing (should not happen in collapsed BDD), print 0
        if (!pVar) { printf("0"); continue; }

        // Get the index used in the BDD manager
        int bddVarIdx = Cudd_Regular(pVar)->index;
        
        // Safety: Prevent array out-of-bounds
        if (bddVarIdx < 0 || bddVarIdx >= Cudd_ReadSize(dd)) {
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
    // Debug 1: Manager
    DdManager * dd = (DdManager *)pNtk->pManFunc;
    if (!dd) { printf("Error: BDD Manager is NULL. Run 'collapse'?\n"); return; }

    // Debug 2: Input BDD
    Abc_Obj_t * pCi = Abc_NtkCi(pNtk, inIdx);
    DdNode * pVar = (DdNode *)pCi->pData;
    if (!pVar) { printf("Error: Input %d has no BDD data.\n", inIdx); return; }

    // Debug 3: Output BDD (Using GlobalBdd helper)
    Abc_Obj_t * pCo = Abc_NtkCo(pNtk, outIdx);
    // Abc_ObjGlobalBdd safely handles phase (negation) and driver lookup
    DdNode * pFunc = (DdNode *)Abc_ObjGlobalBdd(pCo); 
    
    if (!pFunc) { printf("Error: Output %d has no Global BDD.\n", outIdx); return; }

    // Debug 4: Computation
    // Calculate Cofactors: f1 = f | x=1; f0 = f | x=0
    DdNode * f1 = Cudd_Cofactor(dd, pFunc, pVar);       Cudd_Ref(f1);
    DdNode * f0 = Cudd_Cofactor(dd, pFunc, Cudd_Not(pVar)); Cudd_Ref(f0);

    // Debug 5: Comparisons
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
        
        // Debug 6: Pattern Generation
        // Allocate array for cube values
        char * cubeVals = new char[Cudd_ReadSize(dd)];
        
        // Pattern 1: Need (f1=1, f0=0) -> diff1 = f1 & !f0
        DdNode * diff1 = Cudd_bddAnd(dd, f1, Cudd_Not(f0)); Cudd_Ref(diff1);
        
        // Check if diff1 is empty (should not be, if binate)
        if (diff1 != Cudd_ReadLogicZero(dd)) {
             if (Cudd_bddPickOneCube(dd, diff1, cubeVals)) {
                 Lsv_PrintPattern(dd, cubeVals, pNtk, inIdx);
             }
        }
        Cudd_RecursiveDeref(dd, diff1);
        
        // Pattern 2: Need (f1=0, f0=1) -> diff2 = !f1 & f0
        DdNode * diff2 = Cudd_bddAnd(dd, Cudd_Not(f1), f0); Cudd_Ref(diff2);
        
        if (diff2 != Cudd_ReadLogicZero(dd)) {
             if (Cudd_bddPickOneCube(dd, diff2, cubeVals)) {
                 Lsv_PrintPattern(dd, cubeVals, pNtk, inIdx);
             }
        }
        Cudd_RecursiveDeref(dd, diff2);
        
        delete [] cubeVals;
    }

    // Cleanup
    Cudd_RecursiveDeref(dd, f1);
    Cudd_RecursiveDeref(dd, f0);
    
    // Flush to ensure output appears before any subsequent crash
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
    
    // Bounds Checking
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
