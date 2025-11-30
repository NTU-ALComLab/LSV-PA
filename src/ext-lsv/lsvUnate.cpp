/**CFile****************************************************************

  FileName    [lsvUnate.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [lsv: Logic Synthesis and Verification extensions.]

  Synopsis    [Unateness checking using BDDs.]

  Author      [Corrected Implementation]

  Affiliation [NTU]

  Date        [Ver. 3.0. Updated - Nov 30, 2025.]

***********************************************************************/

#include "lsvInt.h"
#include "bdd/cudd/cudd.h"

#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"

extern "C"
{
    Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
}

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     HELPER FUNCTIONS                             ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Prints a BDD cube pattern mapping back to primary inputs.]

  Description [Extracts one cube from the BDD node. Iterates through all
               primary inputs of the network. If the PI is the target 'i',
               prints '-'. Otherwise:
               1. Checks if the PI is a fanin of the driver node.
               2. If yes, uses the fanin index to look up the value in the cube.
               3. If no, prints '0' (don't care/default).]

***********************************************************************/
void Lsv_PrintBddCube(DdManager *dd, DdNode *node, Abc_Ntk_t *pNtk, Abc_Obj_t *pDriver, int targetPiIndex)
{
    // 1. Pick one cube from the BDD node
    // The array 'cube' is indexed by the BDD variable index.
    int nVars = Cudd_ReadSize(dd);
    char *cube = new char[nVars];

    // Safety check: if node is Zero, we can't pick a cube
    if (node == Cudd_ReadZero(dd))
    {
        printf("Error: Empty BDD node passed to PrintCube.\n");
        delete[] cube;
        return;
    }

    // Cudd_bddPickOneCube populates the array: 0 (false), 1 (true), 2 (don't care)
    if (!Cudd_bddPickOneCube(dd, node, cube))
    {
        printf("Error: Failed to pick cube from BDD.\n");
        delete[] cube;
        return;
    }

    // 2. Iterate through PIs in the network order (0 to n-1)
    int nPis = Abc_NtkPiNum(pNtk);
    for (int j = 0; j < nPis; j++)
    {
        // The PI object at index j
        Abc_Obj_t *pPi = Abc_NtkPi(pNtk, j);

        // If this is the variable we are analyzing, print '-'
        if (j == targetPiIndex)
        {
            printf("-");
            continue;
        }

        // We need to find if this PI is in the support of the driver node.
        // In a collapsed BDD network, BDD variable index K corresponds to Fanin K.
        int faninIdx = -1;
        int k;
        Abc_Obj_t *pFanin;

        // Scan fanins of the driver to find pPi
        Abc_ObjForEachFanin(pDriver, pFanin, k)
        {
            if (pFanin == pPi)
            {
                faninIdx = k;
                break;
            }
        }

        if (faninIdx != -1)
        {
            // Found: PI is in support. Get value from cube using fanin index.
            if (faninIdx >= nVars)
            {
                // Safety fallback
                printf("0");
            }
            else
            {
                int val = cube[faninIdx];
                // Val 2 means don't care in the BDD path, default to 0 for specific pattern
                printf(val == 1 ? "1" : "0");
            }
        }
        else
        {
            // Not Found: PI is not in the support of this PO.
            // It is a "don't care", but we must print a specific binary pattern.
            printf("0");
        }
    }
    printf("\n");
    delete[] cube;
}

////////////////////////////////////////////////////////////////////////
///                     COMMAND DEFINITION                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Command to check unateness using BDDs.]

  Description [lsv_unate_bdd <k> <i>
               k: Primary Output Index
               i: Primary Input Index]

***********************************************************************/
int Lsv_CommandUnateBdd(Abc_Frame_t *pAbc, int argc, char **argv)
{

    // --- 1. Argument Parsing ---
    if (argc != 3)
    {
        Abc_Print(-1, "Usage: lsv_unate_bdd <k> <i>\n");
        return 1;
    }

    int k = atoi(argv[1]);
    int i = atoi(argv[2]);

    // --- 2. Network Validation ---
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk)
    {
        Abc_Print(-1, "Error: Empty network.\n");
        return 1;
    }

    // Check if network is functionally BDD (result of 'collapse')
    if (!Abc_NtkIsBddLogic(pNtk))
    {
        Abc_Print(-1, "Error: Network is not in BDD format. Please run 'collapse' first.\n");
        return 1;
    }

    if (k < 0 || k >= Abc_NtkPoNum(pNtk))
    {
        Abc_Print(-1, "Error: Invalid primary output index %d.\n", k);
        return 1;
    }
    if (i < 0 || i >= Abc_NtkPiNum(pNtk))
    {
        Abc_Print(-1, "Error: Invalid primary input index %d.\n", i);
        return 1;
    }

    // --- 3. Identify Objects ---
    Abc_Obj_t *pPi = Abc_NtkPi(pNtk, i);
    Abc_Obj_t *pPo = Abc_NtkPo(pNtk, k);
    Abc_Obj_t *pDriver = Abc_ObjFanin0(pPo);
    int fCompl = Abc_ObjFaninC0(pPo); // Output phase inversion

    // --- 4. Logic Extraction & Analysis ---

    // Case A: PO is driven directly by a PI (e.g. Buffer or Inverter)
    if (Abc_ObjIsPi(pDriver))
    {
        if (pDriver == pPi)
        {
            // Function is y = x (or y = !x)
            // fCompl=0 => y=x (Positive); fCompl=1 => y=!x (Negative)
            printf(fCompl ? "negative unate\n" : "positive unate\n");
        }
        else
        {
            // Function is y = z (where z != x)
            printf("independent\n");
        }
        return 0;
    }

    // Case B: PO is driven by a Logic Node (Standard case for 'collapse')
    if (Abc_ObjIsNode(pDriver))
    {
        DdManager *dd = (DdManager *)pNtk->pManFunc;
        DdNode *ddFunc = (DdNode *)pDriver->pData; // Local BDD

        if (!dd || !ddFunc)
        {
            Abc_Print(-1, "Error: BDD data missing for node.\n");
            return 1;
        }

        // Find the PI in the driver's fanin list to get its BDD variable index.
        // In local BDDs, Fanin Index == BDD Variable Index.
        int bddVarIdx = -1;
        int faninIdx;
        Abc_Obj_t *pFanin;

        Abc_ObjForEachFanin(pDriver, pFanin, faninIdx)
        {
            if (pFanin == pPi)
            {
                bddVarIdx = faninIdx;
                break;
            }
        }

        // If PI is not in the fanin list, the function doesn't depend on it.
        if (bddVarIdx == -1)
        {
            printf("independent\n");
            return 0;
        }

        // Retrieve the BDD variable node
        DdNode *ddVar = Cudd_bddIthVar(dd, bddVarIdx);

        // Apply output phase
        if (fCompl)
            ddFunc = Cudd_Not(ddFunc);

        // --- 5. Perform Cofactoring ---
        // F1 = F | x=1
        // F0 = F | x=0
        DdNode *F1 = Cudd_Cofactor(dd, ddFunc, ddVar);
        Cudd_Ref(F1);
        DdNode *F0 = Cudd_Cofactor(dd, ddFunc, Cudd_Not(ddVar));
        Cudd_Ref(F0);

        // --- 6. Unateness Check ---

        // Independent: F1 == F0
        if (F1 == F0)
        {
            printf("independent\n");
        }
        // Positive Unate: F0 <= F1 (Logic: changing 0->1 can only increase or stay same)
        else if (Cudd_bddLeq(dd, F0, F1))
        {
            printf("positive unate\n");
        }
        // Negative Unate: F1 <= F0
        else if (Cudd_bddLeq(dd, F1, F0))
        {
            printf("negative unate\n");
        }
        // Binate
        else
        {
            printf("binate\n");

            // Pattern 1: Demonstrates Positive Dependency
            // Need m where F(m,0)=0 and F(m,1)=1. m is in (!F0 & F1).
            DdNode *Diff1 = Cudd_bddAnd(dd, Cudd_Not(F0), F1);
            Cudd_Ref(Diff1);
            Lsv_PrintBddCube(dd, Diff1, pNtk, pDriver, i);
            Cudd_RecursiveDeref(dd, Diff1);

            // Pattern 2: Demonstrates Negative Dependency
            // Need m where F(m,0)=1 and F(m,1)=0. m is in (F0 & !F1).
            DdNode *Diff2 = Cudd_bddAnd(dd, F0, Cudd_Not(F1));
            Cudd_Ref(Diff2);
            Lsv_PrintBddCube(dd, Diff2, pNtk, pDriver, i);
            Cudd_RecursiveDeref(dd, Diff2);
        }

        // Cleanup
        Cudd_RecursiveDeref(dd, F1);
        Cudd_RecursiveDeref(dd, F0);
        return 0;
    }

    // Case C: Constant (or Latch, though unlikely in comb logic)
    // If it's a constant, output doesn't change, so it's Independent.
    printf("independent\n");
    return 0;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                     SAT IMPLEMENTATION                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Command to check unateness using SAT.]

  Description [lsv_unate_sat <k> <i>]

***********************************************************************/
int Lsv_CommandUnateSat(Abc_Frame_t *pAbc, int argc, char **argv)
{
    // 1. Argument Parsing
    if (argc != 3)
    {
        Abc_Print(-1, "Usage: lsv_unate_sat <k> <i>\n");
        return 1;
    }
    int k = atoi(argv[1]); // Output index
    int i = atoi(argv[2]); // Input index

    // 2. Network Validation
    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk)
    {
        Abc_Print(-1, "Error: Empty network.\n");
        return 1;
    }
    // SAT requires AIG [cite: 956]
    if (!Abc_NtkIsStrash(pNtk))
    {
        Abc_Print(-1, "Error: Network is not in AIG format (run 'strash' first).\n");
        return 1;
    }

    if (k < 0 || k >= Abc_NtkPoNum(pNtk))
    {
        Abc_Print(-1, "Error: Invalid output index %d.\n", k);
        return 1;
    }
    if (i < 0 || i >= Abc_NtkPiNum(pNtk))
    {
        Abc_Print(-1, "Error: Invalid input index %d.\n", i);
        return 1;
    }

    // 3. Extract Cone [cite: 963]
    Abc_Obj_t *pPo = Abc_NtkPo(pNtk, k);
    Abc_Ntk_t *pCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 1);

    if (Abc_ObjFaninC0(pPo))
    {
        Abc_Obj_t *pPoCone = Abc_NtkPo(pCone, 0);
        Abc_ObjXorFaninC(pPoCone, 0);
    }

    // 4. Convert to CNF [cite: 964, 967]
    Aig_Man_t *pManAig = Abc_NtkToDar(pCone, 0, 0);
    Cnf_Dat_t *pCnf = Cnf_Derive(pManAig, 1);

    // 5. Setup SAT Solver [cite: 965]
    sat_solver *pSat = sat_solver_new();
    sat_solver_setnvars(pSat, pCnf->nVars * 2);

    // Add clauses for Circuit A
    for (int j = 0; j < pCnf->nClauses; j++)
    {
        sat_solver_addclause(pSat, pCnf->pClauses[j], pCnf->pClauses[j + 1]);
    }

    // Lift clauses for Circuit B and add [cite: 969]
    Cnf_DataLift(pCnf, pCnf->nVars);
    for (int j = 0; j < pCnf->nClauses; j++)
    {
        sat_solver_addclause(pSat, pCnf->pClauses[j], pCnf->pClauses[j + 1]);
    }
    Cnf_DataLift(pCnf, -pCnf->nVars);

    // 6. Constrain Shared Inputs [cite: 971]
    Abc_Obj_t *pPiObj;
    int piIdx;

    Abc_NtkForEachPi(pCone, pPiObj, piIdx)
    {
        // Compare with original PI to skip the target variable 'i'
        if (strcmp(Abc_ObjName(pPiObj), Abc_ObjName(Abc_NtkPi(pNtk, i))) == 0)
        {
            continue;
        }

        Aig_Obj_t *pAigPi = Aig_ManCi(pManAig, piIdx);
        int varA = pCnf->pVarNums[pAigPi->Id];
        int varB = varA + pCnf->nVars;

        // Add equality: varA == varB
        sat_solver_add_buffer(pSat, varA, varB, 0);
    }

    // 7. Get Important Variables
    // Find target input in the cone
    int targetA = -1;
    Abc_NtkForEachPi(pCone, pPiObj, piIdx)
    {
        if (strcmp(Abc_ObjName(pPiObj), Abc_ObjName(Abc_NtkPi(pNtk, i))) == 0)
        {
            targetA = pCnf->pVarNums[Aig_ManCi(pManAig, piIdx)->Id];
            break;
        }
    }

    // If input not in cone, it's independent
    if (targetA == -1)
    {
        printf("independent\n");
        sat_solver_delete(pSat);
        Cnf_DataFree(pCnf);
        Aig_ManStop(pManAig);
        Abc_NtkDelete(pCone);
        return 0;
    }

    int targetB = targetA + pCnf->nVars;
    Aig_Obj_t *pAigPo = Aig_ManCo(pManAig, 0);
    int outA = pCnf->pVarNums[pAigPo->Id];
    int outB = outA + pCnf->nVars;

    // 8. Solve
    // Assumptions: targetA=0, targetB=1 [cite: 971]

    // Check 1: Positive Dependency? (Can increasing x increase y?)
    // Condition: targetA=0, targetB=1, outA=0, outB=1
    lit litsPos[4];
    litsPos[0] = toLitCond(targetA, 1); // targetA=0 -> Lit=True
    litsPos[1] = toLitCond(targetB, 0); // targetB=1 -> Lit=True
    litsPos[2] = toLitCond(outA, 1);    // outA=0
    litsPos[3] = toLitCond(outB, 0);    // outB=1

    int isPosDep = (sat_solver_solve(pSat, litsPos, litsPos + 4, 0, 0, 0, 0) == l_True);

    // Store Model for Positive Dependency
    int *modelPos = NULL;
    if (isPosDep)
    {
        modelPos = new int[Abc_NtkPiNum(pNtk)];
        for (int j = 0; j < Abc_NtkPiNum(pNtk); j++)
        {
            if (j == i)
            {
                modelPos[j] = -1;
                continue;
            }
            // Look up PI in cone
            int found = 0;
            int pIdx = 0;
            Abc_Obj_t *pTempPi;
            Abc_NtkForEachPi(pCone, pTempPi, pIdx)
            {
                if (strcmp(Abc_ObjName(pTempPi), Abc_ObjName(Abc_NtkPi(pNtk, j))) == 0)
                {
                    int satVar = pCnf->pVarNums[Aig_ManCi(pManAig, pIdx)->Id];
                    modelPos[j] = sat_solver_var_value(pSat, satVar);
                    found = 1;
                    break;
                }
            }
            if (!found)
                modelPos[j] = 0;
        }
    }

    // Check 2: Negative Dependency? (Can increasing x decrease y?)
    // Condition: targetA=0, targetB=1, outA=1, outB=0
    lit litsNeg[4];
    litsNeg[0] = toLitCond(targetA, 1);
    litsNeg[1] = toLitCond(targetB, 0);
    litsNeg[2] = toLitCond(outA, 0); // outA=1
    litsNeg[3] = toLitCond(outB, 1); // outB=0

    int isNegDep = (sat_solver_solve(pSat, litsNeg, litsNeg + 4, 0, 0, 0, 0) == l_True);

    // Store Model for Negative Dependency
    int *modelNeg = NULL;
    if (isNegDep)
    {
        modelNeg = new int[Abc_NtkPiNum(pNtk)];
        for (int j = 0; j < Abc_NtkPiNum(pNtk); j++)
        {
            if (j == i)
            {
                modelNeg[j] = -1;
                continue;
            }
            int found = 0;
            int pIdx = 0;
            Abc_Obj_t *pTempPi;
            Abc_NtkForEachPi(pCone, pTempPi, pIdx)
            {
                if (strcmp(Abc_ObjName(pTempPi), Abc_ObjName(Abc_NtkPi(pNtk, j))) == 0)
                {
                    int satVar = pCnf->pVarNums[Aig_ManCi(pManAig, pIdx)->Id];
                    modelNeg[j] = sat_solver_var_value(pSat, satVar);
                    found = 1;
                    break;
                }
            }
            if (!found)
                modelNeg[j] = 0;
        }
    }

    // 9. Output Results
    if (isPosDep && isNegDep)
    {
        printf("binate\n");
        // Print Pattern 1 (Pos Dep: 0->1 transition of Y) [cite: 927]
        for (int j = 0; j < Abc_NtkPiNum(pNtk); j++)
        {
            if (modelPos[j] == -1)
                printf("-");
            else
                printf("%d", modelPos[j]);
        }
        printf("\n");
        // Print Pattern 2 (Neg Dep: 1->0 transition of Y) [cite: 928]
        for (int j = 0; j < Abc_NtkPiNum(pNtk); j++)
        {
            if (modelNeg[j] == -1)
                printf("-");
            else
                printf("%d", modelNeg[j]);
        }
        printf("\n");
    }
    else if (isPosDep)
    {
        printf("positive unate\n");
    }
    else if (isNegDep)
    {
        printf("negative unate\n");
    }
    else
    {
        printf("independent\n");
    }

    // 10. Cleanup
    if (modelPos)
        delete[] modelPos;
    if (modelNeg)
        delete[] modelNeg;
    sat_solver_delete(pSat);
    Cnf_DataFree(pCnf);
    Aig_ManStop(pManAig);
    Abc_NtkDelete(pCone);

    return 0;
}

ABC_NAMESPACE_IMPL_END