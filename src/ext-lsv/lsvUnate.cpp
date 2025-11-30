/**
 * @file lsvUnate.cpp
 * @brief BDD Unateness checking (Fixed Input Retrieval)
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
        // The specific input being tested is always "-"
        if (j == inputIdx) {
            printf("-");
            continue;
        }

        // Safety: Prevent accessing outside the cube array
        // In a collapsed network, PI index j corresponds to BDD variable j.
        if (j >= nVars) {
            printf("0"); // Default safe value
            continue;
        }

        // cubeVals[j]: 0=False, 1=True, 2=DontCare
        int val = (int)cubeVals[j];
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

    // 1. Get Input BDD (FIXED: Use Cudd_bddIthVar)
    // Hint 1: Ddnode* var = Cudd_bddIthVar(manager, i);
    DdNode * pVar = Cudd_bddIthVar(dd, inIdx);
    if (!pVar) { 
        fprintf(stderr, "Error: Input BDD var %d not found in manager.\n", inIdx); 
        return; 
    }
    Cudd_Ref(pVar); // Reference it as per hint

    // 2. Get Output BDD
    Abc_Obj_t * pCo = Abc_NtkCo(pNtk, outIdx);
    // Use Abc_ObjGlobalBdd to safely get the driver's function
    DdNode * pFunc = (DdNode *)Abc_ObjGlobalBdd(pCo); 
    
    if (!pFunc) { 
        fprintf(stderr, "Error: Output %d BDD is NULL.\n", outIdx); 
        Cudd_RecursiveDeref(dd, pVar);
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
        int nVars = Cudd_ReadSize(dd);
        if (nVars <= 0) nVars = 1;
        
        std::vector<char> cubeVals(nVars + 10, 2); // Init with 2 (DontCare)

        // Pattern 1: f1=1, f0=0. Need cube in (f1 & !f0)
        DdNode * diff1 = Cudd_bddAnd(dd, f1, Cudd_Not(f0)); Cudd_Ref(diff1);
        if (diff1 != Cudd_ReadLogicZero(dd)) {
             if (Cudd_bddPickOneCube(dd, diff1, cubeVals.data())) {
                 Lsv_PrintPattern(dd, cubeVals.data(), nVars, pNtk, inIdx);
             }
        }
        Cudd_RecursiveDeref(dd, diff1);
        
        // Pattern 2: f1=0, f0=1. Need cube in (!f1 & f0)
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
    Cudd_RecursiveDeref(dd, pVar); // Deref pVar as we Ref'd it manually
    
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
    
    // Bounds check
    if (outIdx < 0 || outIdx >= Abc_NtkCoNum(pNtk)) {
        printf("Error: Invalid output index %d\n", outIdx);
        return 1;
    }
    if (inIdx < 0 || inIdx >= Abc_NtkCiNum(pNtk)) {
        printf("Error: Invalid input index %d\n", inIdx);
        return 1;
    }

    if (!Abc_NtkIsBddLogic(pNtk)) { 
        printf("Error: Network not in BDD format. Run 'collapse' first.\n"); 
        return 1; 
    }
    
    Lsv_NtkUnateBdd(pNtk, outIdx, inIdx);
    return 0;
}
