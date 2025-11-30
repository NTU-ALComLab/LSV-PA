/**
 * @file lsvUnate.cpp
 * @brief BDD Unateness checking for LSV PA2 (Part 1)
 */

#include <vector>
#include <cstdio>
#include <cstdlib>
#include <cstdint>

// Define pointer types if missing in your environment (Safe for Colab/Linux)
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
    
    // Iterate over all Primary Inputs to print the pattern
    for (int j = 0; j < nInputs; j++) {
        // 1. The specific input x_i being tested is always "-" 
        if (j == inputIdx) {
            printf("-");
            continue;
        }

        // 2. For other inputs, we retrieve the value from the cube.
        // Assumption: In a collapsed network, PI index 'j' maps to BDD variable index 'j'.
        // This is standard for 'collapse' and consistent with Cudd_bddIthVar logic.
        int bddVarIdx = j;

        // Safety check: prevent array out-of-bounds if manager size < nInputs
        if (bddVarIdx >= nVars) {
            printf("0"); // Default safe value
            continue;
        }

        // cubeVals[idx] is 0 (False), 1 (True), or 2 (Don't Care)
        //  requires 0 or 1. We treat Don't Care as 0.
        int val = (int)cubeVals[bddVarIdx];
        
        if (val == 1) {
            printf("1");
        } else {
            printf("0"); 
        }
    }
    printf("\n");
}

// -----------------------------------------------------------------------------
// Main Logic
// -----------------------------------------------------------------------------

void Lsv_NtkUnateBdd(Abc_Ntk_t * pNtk, int outIdx, int inIdx) {
    // 1. Get BDD Manager
    DdManager * dd = (DdManager *)pNtk->pManFunc;
    if (!dd) { 
        printf("Error: BDD Manager is NULL. Run 'collapse' first.\n"); 
        return; 
    }

    // 2. Get Input BDD Variable 
    // Use Cudd_bddIthVar instead of pCi->pData to match Hint 1 and avoid NULL errors.
    DdNode * pVar = Cudd_bddIthVar(dd, inIdx);
    if (!pVar) {
        printf("Error: Input index %d out of BDD bounds.\n", inIdx);
        return;
    }
    // Hint 1: Ref the variable [cite: 37]
    Cudd_Ref(pVar); 
    
    // 3. Get Output BDD Function
    Abc_Obj_t * pCo = Abc_NtkCo(pNtk, outIdx);
    // Abc_ObjGlobalBdd retrieves the function from the driver node safely, 
    // handling potential complement pointers (inverted outputs).
    DdNode * pFunc = (DdNode *)Abc_ObjGlobalBdd(pCo);
    
    if (!pFunc) { 
        printf("Error: Output BDD is NULL.\n"); 
        Cudd_RecursiveDeref(dd, pVar); // Cleanup before return
        return; 
    }

    // 4. Compute Cofactors: f1 (x_i=1) and f0 (x_i=0)
    // Note: Cudd_Cofactor returns a new node, so we must Ref it. 
    DdNode * f1 = Cudd_Cofactor(dd, pFunc, pVar);           Cudd_Ref(f1);
    DdNode * f0 = Cudd_Cofactor(dd, pFunc, Cudd_Not(pVar)); Cudd_Ref(f0);

    // 5. Check Relations
    if (f1 == f0) {
        printf("independent\n"); // [cite: 18]
    } 
    else if (Cudd_bddLeq(dd, f0, f1)) {
        printf("positive unate\n"); // [cite: 16]
    } 
    else if (Cudd_bddLeq(dd, f1, f0)) {
        printf("negative unate\n"); // [cite: 17]
    } 
    else {
        printf("binate\n"); // [cite: 20]
        
        // 6. Generate Patterns for Binate case
        // Get number of variables to size the array safely
        int nVars = Cudd_ReadSize(dd);
        
        // Use vector for automatic memory cleanup
        std::vector<char> cubeVals(nVars, 2); 

        // --- Pattern 1: f1=1, f0=0 ---
        // We need a cube in (f1 & !f0). Cofactoring w.r.t this cube gives x_i. [cite: 24]
        DdNode * diff1 = Cudd_bddAnd(dd, f1, Cudd_Not(f0)); Cudd_Ref(diff1);
        
        if (diff1 != Cudd_ReadLogicZero(dd)) {
             // Cudd_bddPickOneCube populates 'cubeVals' with 0, 1, or 2
             if (Cudd_bddPickOneCube(dd, diff1, cubeVals.data())) {
                 Lsv_PrintPattern(dd, cubeVals.data(), nVars, pNtk, inIdx);
             }
        }
        Cudd_RecursiveDeref(dd, diff1);
        
        // --- Pattern 2: f1=0, f0=1 ---
        // We need a cube in (!f1 & f0). Cofactoring w.r.t this cube gives !x_i. [cite: 24]
        DdNode * diff2 = Cudd_bddAnd(dd, Cudd_Not(f1), f0); Cudd_Ref(diff2);
        
        if (diff2 != Cudd_ReadLogicZero(dd)) {
             if (Cudd_bddPickOneCube(dd, diff2, cubeVals.data())) {
                 Lsv_PrintPattern(dd, cubeVals.data(), nVars, pNtk, inIdx);
             }
        }
        Cudd_RecursiveDeref(dd, diff2);
    }

    // Cleanup Cofactors 
    Cudd_RecursiveDeref(dd, f1);
    Cudd_RecursiveDeref(dd, f0);
    Cudd_RecursiveDeref(dd, pVar); 
    
    // Ensure output is flushed immediately
    fflush(stdout);
}

int Lsv_CommandUnateBdd(Abc_Frame_t * pAbc, int argc, char ** argv) {
    // Check format [cite: 13]
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
    
    // Check if network is BDD 
    if (!Abc_NtkIsBddLogic(pNtk)) { 
        printf("Error: Network not in BDD format. Run 'collapse' first.\n"); 
        return 1; 
    }
    
    // Bounds Check [cite: 14]
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
