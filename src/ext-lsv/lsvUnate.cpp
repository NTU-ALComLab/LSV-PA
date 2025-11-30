/**
 * @file lsvUnate.cpp
 * @brief Implementation of BDD and SAT unateness checking for LSV PA2.
 */

#include "lsv.h"
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

// -----------------------------------------------------------------------------
// BDD Unateness Checker Implementation
// -----------------------------------------------------------------------------

/**
 * @brief Helper to print a specific input pattern based on a BDD cube.
 * * @param dd The CUDD manager.
 * @param cube The BDD node representing the cube (one path in the BDD).
 * @param pNtk The ABC network.
 * @param inputIdx The index of the primary input x_i being tested.
 */
void Lsv_PrintPattern(DdManager * dd, DdNode * cube, Abc_Ntk_t * pNtk, int inputIdx) {
    int nInputs = Abc_NtkCiNum(pNtk);
    for (int j = 0; j < nInputs; j++) {
        // For the specific variable x_i being tested, we must print "-"
        if (j == inputIdx) {
            printf("-");
            continue;
        }

        // Get the BDD variable corresponding to the j-th PI
        Abc_Obj_t * pVarObj = Abc_NtkCi(pNtk, j);
        DdNode * pVar = (DdNode *)pVarObj->pData; 
        
        // Check if the variable j exists in the cube
        if (Cudd_bddLeq(dd, cube, pVar)) {
            // If cube implies var, then var must be 1
            printf("1");
        } 
        else if (Cudd_bddLeq(dd, cube, Cudd_Not(pVar))) {
            // If cube implies !var, then var must be 0
            printf("0");
        } 
        else {
            // Variable is not in the cube (Don't Care).
            // The prompt requires specific assignments (0 or 1), so we default to 0.
            printf("0");
        }
    }
    printf("\n");
}

void Lsv_NtkUnateBdd(Abc_Ntk_t * pNtk, int outIdx, int inIdx) {
    DdManager * dd = (DdManager *)pNtk->pManFunc;
    
    // Get BDD for input x_i
    Abc_Obj_t * pCi = Abc_NtkCi(pNtk, inIdx);
    DdNode * pVar = (DdNode *)pCi->pData;
    
    // Get BDD for output y_k
    Abc_Obj_t * pCo = Abc_NtkCo(pNtk, outIdx);
    // In collapsed BDD networks, the driver of the CO holds the function
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
        
        // Pattern 1: f1=1, f0=0. Find cube in (f1 & !f0)
        DdNode * diff1 = Cudd_bddAnd(dd, f1, Cudd_Not(f0)); Cudd_Ref(diff1);
        DdNode * cube1 = Cudd_bddPickOneCube(dd, diff1);    Cudd_Ref(cube1);
        Lsv_PrintPattern(dd, cube1, pNtk, inIdx);
        Cudd_RecursiveDeref(dd, diff1);
        Cudd_RecursiveDeref(dd, cube1);
        
        // Pattern 2: f1=0, f0=1. Find cube in (!f1 & f0)
        DdNode * diff2 = Cudd_bddAnd(dd, Cudd_Not(f1), f0); Cudd_Ref(diff2);
        DdNode * cube2 = Cudd_bddPickOneCube(dd, diff2);    Cudd_Ref(cube2);
        Lsv_PrintPattern(dd, cube2, pNtk, inIdx);
        Cudd_RecursiveDeref(dd, diff2);
        Cudd_RecursiveDeref(dd, cube2);
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
    
    // Sanity Checks
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