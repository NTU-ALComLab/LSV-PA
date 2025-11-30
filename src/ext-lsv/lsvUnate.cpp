/**
 * @file lsvUnate.cpp
 * @brief Implementation of BDD unateness checking for LSV PA2.
 */

#include "lsv.h"
#include "base/abc/abc.h"
#include "bdd/cudd/cudd.h"

// -----------------------------------------------------------------------------
// Helper Function
// -----------------------------------------------------------------------------

/**
 * @brief Prints the input pattern based on the cube array filled by CUDD.
 * * @param dd The CUDD manager.
 * @param cubeVals The char array filled by Cudd_bddPickOneCube. 
 * cubeVals[i] is 0 (false), 1 (true), or 2 (don't care).
 * @param pNtk The ABC network.
 * @param inputIdx The index of the primary input x_i being tested.
 */
void Lsv_PrintPattern(DdManager * dd, char * cubeVals, Abc_Ntk_t * pNtk, int inputIdx) {
    int nInputs = Abc_NtkCiNum(pNtk);
    for (int j = 0; j < nInputs; j++) {
        // For the specific variable x_i being tested, we must print "-"
        if (j == inputIdx) {
            printf("-");
            continue;
        }

        // Get the BDD variable index corresponding to the j-th PI
        Abc_Obj_t * pVarObj = Abc_NtkCi(pNtk, j);
        DdNode * pVar = (DdNode *)pVarObj->pData;
        int bddVarIdx = Cudd_Regular(pVar)->index;
        
        // Check the value in the cube array
        int val = (int)cubeVals[bddVarIdx];
        
        if (val == 0) {
            printf("0");
        } else if (val == 1) {
            printf("1");
        } else {
            // val == 2 means Don't Care.
            // The assignment asks for a concrete assignment (0 or 1). We pick 0.
            printf("0");
        }
    }
    printf("\n");
}

// -----------------------------------------------------------------------------
// Main Function
// -----------------------------------------------------------------------------

void Lsv_NtkUnateBdd(Abc_Ntk_t * pNtk, int outIdx, int inIdx) {
    DdManager * dd = (DdManager *)pNtk->pManFunc;
    
    // Get BDD for input x_i
    Abc_Obj_t * pCi = Abc_NtkCi(pNtk, inIdx);
    DdNode * pVar = (DdNode *)pCi->pData;
    
    // Get BDD for output y_k
    Abc_Obj_t * pCo = Abc_NtkCo(pNtk, outIdx);
    Abc_Obj_t * pDriver = Abc_ObjFanin0(pCo);
    DdNode * pFunc = (DdNode *)pDriver->pData;
    
    // Adjust for complement pointer if the edge to CO is inverted
    if (Abc_ObjFaninC0(pCo)) {
        pFunc = Cudd_Not(pFunc);
    }
    
    // Compute Cofactors: f1 (x_i=1) and f0 (x_i=0)
    DdNode * f1 = Cudd_Cofactor(dd, pFunc, pVar);       Cudd_Ref(f1);
    DdNode * f0 = Cudd_Cofactor(dd, pFunc, Cudd_Not(pVar)); Cudd_Ref(f0);
    
    // Check Relations
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
        
        // Allocate buffer for Cudd_bddPickOneCube
        // The size must be equal to the number of BDD variables in the manager
        char * cubeVals = new char[Cudd_ReadSize(dd)];

        // --- Pattern 1: f1=1, f0=0 ---
        // We need a cube inside the set difference (f1 & !f0)
        DdNode * diff1 = Cudd_bddAnd(dd, f1, Cudd_Not(f0)); Cudd_Ref(diff1);
        
        // Pick one cube from diff1. 
        // Note: The function returns 1 on success, 0 on failure. It fills cubeVals.
        if (Cudd_bddPickOneCube(dd, diff1, cubeVals)) {
            Lsv_PrintPattern(dd, cubeVals, pNtk, inIdx);
        }
        Cudd_RecursiveDeref(dd, diff1);
        
        // --- Pattern 2: f1=0, f0=1 ---
        // We need a cube inside the set difference (!f1 & f0)
        DdNode * diff2 = Cudd_bddAnd(dd, Cudd_Not(f1), f0); Cudd_Ref(diff2);
        
        // Pick one cube from diff2
        if (Cudd_bddPickOneCube(dd, diff2, cubeVals)) {
            Lsv_PrintPattern(dd, cubeVals, pNtk, inIdx);
        }
        Cudd_RecursiveDeref(dd, diff2);
        
        // Clean up memory
        delete [] cubeVals;
    }
    
    Cudd_RecursiveDeref(dd, f1);
    Cudd_RecursiveDeref(dd, f0);
}

int Lsv_CommandUnateBdd(Abc_Frame_t * pAbc, int argc, char ** argv) {
    if (argc != 3) {
        printf("Usage: lsv_unate_bdd <out_index> <in_index>\n");
        return 1;
    }
    
    int outIdx = atoi(argv[1]);
    int inIdx = atoi(argv[2]);
    
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    if (pNtk == NULL) {
        printf("Error: Empty network.\n");
        return 1;
    }
    
    if (!Abc_NtkIsBddLogic(pNtk)) {
        printf("Error: Network is not in BDD format. Run 'collapse' first.\n");
        return 1;
    }
    
    if (outIdx < 0 || outIdx >= Abc_NtkCoNum(pNtk)) {
        printf("Error: Invalid output index.\n");
        return 1;
    }
    if (inIdx < 0 || inIdx >= Abc_NtkCiNum(pNtk)) {
        printf("Error: Invalid input index.\n");
        return 1;
    }
    
    Lsv_NtkUnateBdd(pNtk, outIdx, inIdx);
    return 0;
}
