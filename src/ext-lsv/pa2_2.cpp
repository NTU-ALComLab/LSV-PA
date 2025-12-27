#include "base/abc/abc.h"
#include "base/main/main.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"

extern "C" {
    Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}

void Lsv_PrintSatPattern(Abc_Ntk_t* pNtk, Aig_Man_t* pAig, Cnf_Dat_t* pCnf, 
                         sat_solver* pSat, int targetPiIndex) 
{
    int nPis = Abc_NtkPiNum(pNtk);
    
    // Initialize output pattern
    char* pattern = new char[nPis + 1];
    pattern[nPis] = '\0';

    for (int j = 0; j < nPis; j++) {
        if (j == targetPiIndex) {
            pattern[j] = '-';
        } 
        else {

            Aig_Obj_t* pObjPi = Aig_ManCi(pAig, j);
            int varId = pCnf->pVarNums[pObjPi->Id]; 

            int val = sat_solver_var_value(pSat, varId);
            pattern[j] = (val == 1) ? '1' : '0';
        }
    }

    printf("%s\n", pattern);
    delete[] pattern;
}

void Lsv_Sat_AddEqual(sat_solver* pSat, int varA, int varB) {
    // Clause 1: ~varA + varB
    lit Lits[2];
    Lits[0] = toLitCond(varA, 1); 
    Lits[1] = toLitCond(varB, 0); 
    sat_solver_addclause(pSat, Lits, Lits + 2);

    // Clause 2: varA + ~varB
    Lits[0] = toLitCond(varA, 0);
    Lits[1] = toLitCond(varB, 1);
    sat_solver_addclause(pSat, Lits, Lits + 2);
}

int pa2_2(Abc_Frame_t* pAbc, int argc, char** argv) {
    // lsv_unate_sat <k> <i>
    if (argc != 3) {
        Abc_Print(-1, "Usage: lsv_unate_sat <k> <i>\n");
        return 1;
    }

    int k = atoi(argv[1]); // Output index
    int i = atoi(argv[2]); // Input index

    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Empty Network.\n");
        return 1;
    }

    // Po: Output number, Pi: Input number checking
    if (k < 0 || k >= Abc_NtkPoNum(pNtk)) {
        Abc_Print(-1, "Invalid output index.\n");
        return 1;
    }
    if (i < 0 || i >= Abc_NtkPiNum(pNtk)) {
        Abc_Print(-1, "Invalid input index.\n");
        return 1;
    }

    // Prepare AIG for SAT
    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
    Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 1);
    Aig_Man_t* pAig = Abc_NtkToDar(pCone, 0, 0);

    // Initialize SAT Solver and CNF
    sat_solver* pSat = sat_solver_new();
    Cnf_Dat_t* pCnf = Cnf_Derive(pAig, Aig_ManCoNum(pAig));

    // Write Copy A (Original)
    Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);

    // Write Copy B (Lifted)
    int shift = pCnf->nVars;
    Cnf_DataLift(pCnf, shift);
    Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
    Cnf_DataLift(pCnf, -shift); // Restore pCnf

    // Add Equivalence Constraints for all inputs except target i
    int nPis = Abc_NtkPiNum(pNtk);
    for (int j = 0; j < nPis; j++) {
        if (j == i) continue; // Skip target variable

        Aig_Obj_t* pObjPi = Aig_ManCi(pAig, j);
        int varA = pCnf->pVarNums[pObjPi->Id];
        int varB = varA + shift;
        Lsv_Sat_AddEqual(pSat, varA, varB);
    }

    // Get Variable IDs for assumptions
    Aig_Obj_t* pObjXi = Aig_ManCi(pAig, i);
    Aig_Obj_t* pObjYk = Aig_ManCo(pAig, 0); // Cone has 1 PO

    int varXi_A = pCnf->pVarNums[pObjXi->Id];
    int varXi_B = varXi_A + shift;
    int varYk_A = pCnf->pVarNums[pObjYk->Id];
    int varYk_B = varYk_A + shift;

    // --- Check Unateness ---
    
    // Check Negative Behavior (Rising edge causes Falling edge): x: 0->1, y: 1->0
    // Violation of Positive Unateness
    lit assumpsNegBehavior[4];
    assumpsNegBehavior[0] = toLitCond(varXi_A, 1); // 0
    assumpsNegBehavior[1] = toLitCond(varXi_B, 0); // 1
    assumpsNegBehavior[2] = toLitCond(varYk_A, 0); // 1
    assumpsNegBehavior[3] = toLitCond(varYk_B, 1); // 0

    int statusNegBehavior = sat_solver_solve(pSat, assumpsNegBehavior, assumpsNegBehavior + 4, 0, 0, 0, 0);
    int isPosUnate = (statusNegBehavior == l_False); // UNSAT means no counter-example found

    // Check Positive Behavior (Rising edge causes Rising edge): x: 0->1, y: 0->1
    // Violation of Negative Unateness
    lit assumpsPosBehavior[4];
    assumpsPosBehavior[0] = toLitCond(varXi_A, 1); // 0
    assumpsPosBehavior[1] = toLitCond(varXi_B, 0); // 1
    assumpsPosBehavior[2] = toLitCond(varYk_A, 1); // 0
    assumpsPosBehavior[3] = toLitCond(varYk_B, 0); // 1

    int statusPosBehavior = sat_solver_solve(pSat, assumpsPosBehavior, assumpsPosBehavior + 4, 0, 0, 0, 0);
    int isNegUnate = (statusPosBehavior == l_False); // UNSAT means no counter-example found

    // Output Results (Logic matches BDD version)
    if (isPosUnate && isNegUnate) {
        printf("independent\n");
    } 
    else if (isPosUnate) {
        printf("positive unate\n");
    } 
    else if (isNegUnate) {
        printf("negative unate\n");
    } 
    else {
        printf("binate\n");
        // Print Binate Patterns
        
        // Pattern 1: x: 0->1, y: 0->1 (Matches Logic of BDD diff1)
        // Corresponds to Positive Behavior (Violation of Neg Unate)
        if (statusPosBehavior == l_True) {
            // Re-solve to ensure model is loaded
            sat_solver_solve(pSat, assumpsPosBehavior, assumpsPosBehavior + 4, 0, 0, 0, 0);
            Lsv_PrintSatPattern(pNtk, pAig, pCnf, pSat, i);
        }

        // Pattern 2: x: 0->1, y: 1->0 (Matches Logic of BDD diff2)
        // Corresponds to Negative Behavior (Violation of Pos Unate)
        if (statusNegBehavior == l_True) {
            // Re-solve to ensure model is loaded
            sat_solver_solve(pSat, assumpsNegBehavior, assumpsNegBehavior + 4, 0, 0, 0, 0);
            Lsv_PrintSatPattern(pNtk, pAig, pCnf, pSat, i);
        }
    }

    // Cleanup
    sat_solver_delete(pSat);
    Cnf_DataFree(pCnf);
    Aig_ManStop(pAig);
    Abc_NtkDelete(pCone);

    return 0;
}