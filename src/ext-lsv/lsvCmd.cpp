#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

extern "C" {
#include "bdd/cudd/cudd.h"
}

#include <cstdio>
#include <functional>
#include <cstdlib>
extern "C" {
#include "base/abc/abc.h"
#include "aig/aig/aig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"       // or correct sat header for your ABC
}
#include <vector>
#include <assert.h>
#include <string>
#include <cstring>



extern "C" {
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);


////////////////////////////////////////////////////////////////////////
/// Registration
////////////////////////////////////////////////////////////////////////
void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
}
void destroy(Abc_Frame_t* pAbc) {}
Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

static void PrintPattern(Abc_Ntk_t* pNtk, int skipPi, const std::vector<int>& assign, std::vector<int>& bddvar) {
    int piCount = Abc_NtkPiNum(pNtk);
    for (int j = 0; j < piCount; j++) {
        if (j == skipPi) printf("-");
        else printf("%d", assign[bddvar[j]]);
    }
    printf("\n");
}

static void PrintOneCube(DdManager* dd, DdNode* f, int nVars, const char* name) {
    // Print all cubes (cover) of a BDD
    std::vector<int> cube(nVars, -1); // -1 = don't care

    printf("All cubes of %s:\n", name);

    // Recursive helper
    std::function<void(DdNode*, int)> Enumerate = [&](DdNode* node, int varIndex) {
        if (node == Cudd_ReadLogicZero(dd)) return; // no cube
        if (node == Cudd_ReadOne(dd)) {             // reached terminal 1
            for (int v : cube) {
                if (v == -1) printf("-");
                else printf("%d", v);
            }
            printf("\n");
            return;
        }

        // Get the variable index of the top node, which is the BDD var ID
        int topVar = Cudd_NodeReadIndex(node);

        // Recursive call needs to start from the BDD variable index, not varIndex
        // The BDD variable IDs typically correspond to the PI indices
        
        // branch 0 (complemented edge in CUDD means the variable is complemented)
        cube[topVar] = 0;
        Enumerate(Cudd_E(node), topVar + 1); // Cudd_E (Else/Low) is the complement edge

        // branch 1
        cube[topVar] = 1;
        Enumerate(Cudd_T(node), topVar + 1); // Cudd_T (Then/High) is the positive edge

        // restore don't care
        cube[topVar] = -1;
    };

    // The current BDD variables are mapped to the PI indices 0 to nVars-1
    Enumerate(f, 0);
}
/*
void PrintMinterms_rec(DdManager* dd, DdNode* f, int level, int* arr)
{
    // Terminal cases
    if (f == Cudd_ReadOne(dd)) {
        // print minterm
        for (int i = 0; i < Cudd_ReadSize(dd); i++)
            printf("%d ", arr[i]);
        printf("\n");
        return;
    }
    if (f == Cudd_ReadLogicZero(dd)) {
        return;
    }

    int var = Cudd_NodeReadIndex(f);
    DdNode *T = Cudd_T(f);
    DdNode *E = Cudd_E(f);

    // descend on T (xi = 1)
    arr[var] = 1;
    PrintMinterms_rec(dd, Cudd_Regular(T), level+1, arr);

    // descend on E (xi = 0)
    arr[var] = 0;
    if (Cudd_IsComplement(E))
        PrintMinterms_rec(dd, Cudd_Not(Cudd_Regular(E)), level+1, arr);
    else
        PrintMinterms_rec(dd, E, level+1, arr);
}

void PrintMinterms(DdManager* dd, DdNode* f)
{
    int n = Cudd_ReadSize(dd);
    int* arr = (int*)calloc(n, sizeof(int));
    printf("Minterms of f:\n");
    PrintMinterms_rec(dd, f, 0, arr);
    free(arr);
}
*/


/**
 * @brief Prints a single minterm (full assignment of 0s and 1s).
 * @param assignments The vector containing the assignment for all PI variables.
 */
void printAssignment(const std::vector<int>& assignments) {
    printf("Minterm: (");
    for (size_t i = 0; i < assignments.size(); ++i) {
        if (i > 0) printf(", ");
        printf("x%zu=%d", i, assignments[i]);
    }
    printf(")\n");
}

/**
 * @brief Recursively traverses the BDD and expands 'don't care' variables 
 * to ensure only full minterms (no 2s or -1s) are printed.
 *
 * @param dd The CUDD manager.
 * @param node The current BDD node.
 * @param assignments Vector storing the current assignment (must be size nVars).
 * @param globalLevel The current PI index we are considering (0 to nVars-1).
 * @param nVars Total number of variables in the manager.
 */
void printAllMintermsRecursive(
    DdManager* dd,
    DdNode* node,
    std::vector<int>& assignments,
    int globalLevel,
    int nVars
) {
    // A. Terminal Case 1: Reached a constant node (0 or 1)
    if (Cudd_IsConstant(Cudd_Regular(node))) {
        // If the path leads to 1 (True) and is not complemented.
        if (Cudd_Regular(node) == Cudd_ReadOne(dd) && !Cudd_IsComplement(node)) {
            
            // The function is TRUE from this point down.
            // We must now fill in all remaining variables (globalLevel to nVars-1) 
            // with both 0 and 1 to generate all minterms covered by this cube.
            
            if (globalLevel == nVars) {
                // All variables are assigned. This is a complete minterm.
                printAssignment(assignments);
                return;
            }

            // Fill the rest with 0s and 1s (forcing minterm expansion)
            assignments[globalLevel] = 0;
            printAllMintermsRecursive(dd, node, assignments, globalLevel + 1, nVars);
            
            assignments[globalLevel] = 1;
            printAllMintermsRecursive(dd, node, assignments, globalLevel + 1, nVars);
            
            // Backtrack the last assignment
            assignments[globalLevel] = -1; 
        }
        return;
    }

    // B. Handling BDD Variable Index vs. Global Level
    DdNode* regularNode = Cudd_Regular(node);
    int varIndex = Cudd_NodeReadIndex(regularNode);

    // Case 1: The BDD skips variables (Don't Cares)
    // If the BDD's decision variable (varIndex) is HIGHER than the current 
    // expected global variable (globalLevel), it means the BDD is constant 
    // over all variables between globalLevel and varIndex-1.
    // We must manually branch on the current globalLevel variable to force minterm expansion.
    if (varIndex > globalLevel) {
        // Branch for current variable (globalLevel) = 0
        assignments[globalLevel] = 0;
        printAllMintermsRecursive(dd, node, assignments, globalLevel + 1, nVars);

        // Branch for current variable (globalLevel) = 1
        assignments[globalLevel] = 1;
        printAllMintermsRecursive(dd, node, assignments, globalLevel + 1, nVars);

        // Backtrack
        assignments[globalLevel] = -1;
        return; 
    }

    // Case 2: The BDD makes a decision on the current variable (varIndex == globalLevel)
    
    // Path 1: Negative Cofactor (Set variable to 0)
    assignments[varIndex] = 0;
    DdNode* child0 = Cudd_IsComplement(node) ? Cudd_Not(Cudd_E(regularNode)) : Cudd_E(regularNode);
    printAllMintermsRecursive(dd, child0, assignments, globalLevel + 1, nVars);
    
    // Path 2: Positive Cofactor (Set variable to 1)
    assignments[varIndex] = 1;
    DdNode* child1 = Cudd_IsComplement(node) ? Cudd_Not(Cudd_T(regularNode)) : Cudd_T(regularNode);
    printAllMintermsRecursive(dd, child1, assignments, globalLevel + 1, nVars);

    // Backtrack: Reset the assignment for the parent node's next path
    assignments[varIndex] = -1; 
}


/**
 * @brief Public wrapper function to start the minterm printing traversal.
 *
 * @param dd The CUDD manager.
 * @param f The BDD node for the function (e.g., f0 or f1).
 * @param nVars Total number of variables in the manager.
 */
void PrintMinterms(DdManager* dd, DdNode* f)
{
    // Retrieve nVars from the BDD manager size
    int nVars = Cudd_ReadSize(dd);
    const char* label = "BDD Function"; // Using a generic label

    // Check for constant zero function
    if (Cudd_Regular(f) == Cudd_ReadLogicZero(dd)) {
        Abc_Print(0, "Function %s is constant 0 (no minterms).\n", label);
        return;
    }

    // Initialize the assignment vector with -1 (unassigned)
    std::vector<int> assignments(nVars, -1);
    
    printf("\n--- Minterms for %s (Total variables: %d) ---\n", label, nVars);
    
    // Start the recursive traversal from level 0
    printAllMintermsRecursive(dd, f, assignments, 0, nVars);
    
    printf("--------------------------------------------------\n");
}



////////////////////////////////////////////////////////////////////////
/// MAIN COMMAND
////////////////////////////////////////////////////////////////////////
int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv)
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "No network loaded.\n");
        return 1;
    }

    if (argc != 3) {
        Abc_Print(-1, "usage: lsv_unate_bdd <po index> <pi index>\n");
        return 1;
    }

    int k = atoi(argv[1]); // PO index
    int i = atoi(argv[2]); // PI index
    int nVars = Abc_NtkPiNum(pNtk);

    if (k < 0 || k >= Abc_NtkPoNum(pNtk)) {
        Abc_Print(-1, "PO index out of range.\n");
        return 1;
    }
    if (i < 0 || i >= nVars) {
        Abc_Print(-1, "PI index out of range.\n");
        return 1;
    }


// Build global BDDs if needed
if (!pNtk->pManFunc) {
    Abc_Print(-1, "Building global BDDs...\n");
    Abc_NtkBuildGlobalBdds(pNtk, 10000000, 0, 0, 0, 0); // correct signature

    if (!pNtk->pManFunc) {
        Abc_Print(-1, "ERROR: pManFunc is STILL NULL after global BDD build.\n");
        return 1;
    }
}

    DdManager* dd = (DdManager*)pNtk->pManFunc;

    // Correct: PO does NOT contain BDD → get BDD of its fanin
    Abc_Obj_t* po = Abc_NtkPo(pNtk, k);
    Abc_Obj_t* root = Abc_ObjFanin0(po);
    int isInverted_bdd= Abc_ObjFaninC0(po);
    if (!root) {
        Abc_Print(-1, "PO has no fanin.\n");
        return 1;
    }

    //Abc_Print(-2, "invert: %d\n", isInverted_bdd);
    // Correct way to retrieve global BDD
    DdNode* f = (DdNode*)root->pData;
    
    //Abc_Print(-2, "DEBUG: p2\n");
    if (!f) {
        Abc_Print(-1, "Global BDD not available.\n");
        return 1;
    }
    if (isInverted_bdd) f= Cudd_Not(f);

    Cudd_Ref(f);

    std::vector<int> bddvar(nVars,0);

    for(int jk =0; jk<nVars; jk++){

      Abc_Obj_t* pCi = Abc_NtkCi(pNtk, jk);
        const char* piName = Abc_ObjName(pCi);

        Vec_Ptr_t* vFaninNames = Abc_NodeGetFaninNames(root);
        char** bdd2name_arr = (char**)vFaninNames->pArray;
        int bdd_num = Abc_ObjFaninNum(root);

        
        int bddLevel = -1;
        for (int j = 0; j < bdd_num; j++) {
          if (strcmp(bdd2name_arr[j], piName) == 0) {
            //Abc_Print(-2,"%s j:%d\n",piName,j);
            bddvar[jk] = j;
            break;
          }
        }
    }
    

    



    //int bddIndex = pNtk->vVars->pArray[i]; 
    DdNode* xi = Cudd_bddIthVar(dd, bddvar[i]);


/*
    // Correct: Cudd_bddIthVar already has permanent ref
    DdNode* xi = Cudd_bddIthVar(dd, i);
    Cudd_Ref(xi);   // we add local reference so we can deref later*/

    // Cofactors f0, f1
    DdNode* f1 = Cudd_Cofactor(dd, f, xi);
    Cudd_Ref(f1);

    // f0 = f with x_i = 0
    // Cofactor(f, !x_i) = assume x_i = 0
    DdNode* f0 = Cudd_Cofactor(dd, f, Cudd_Not(xi));
    Cudd_Ref(f0);


    // Unateness test
    bool pos = Cudd_bddLeq(dd, f0, f1);
    bool neg = Cudd_bddLeq(dd, f1, f0);
/*
    PrintMinterms(dd, f0);
    PrintMinterms(dd, f1);

    Abc_Print(-2, "pos=%d neg=%d.\n",pos,neg);

*/
    if (pos && !neg) printf("positive unate\n");
    else if (neg && !pos) printf("negative unate\n");
    else if (pos && neg) printf("independent\n");
    else {
        printf("binate\n");

        // Witnesses
        DdNode* w1 = Cudd_bddAnd(dd, f1, Cudd_Not(f0)); Cudd_Ref(w1);
        DdNode* w2 = Cudd_bddAnd(dd, f0, Cudd_Not(f1)); Cudd_Ref(w2);

        char* arr1 = new char[nVars];
        char* arr2 = new char[nVars];
        for (int j = 0; j < nVars; j++) arr1[j] = arr2[j] = -1;

        int ok1 = Cudd_bddPickOneCube(dd, w1, arr1);
        int ok2 = Cudd_bddPickOneCube(dd, w2, arr2);

        if (!ok1 || !ok2) {
            Abc_Print(-1, "Error: cannot find binate witness.\n");
        } else {
            std::vector<int> pat1(nVars), pat2(nVars);
            for (int j = 0; j < nVars; j++) {
                pat1[j] = arr1[j];
                pat2[j] = arr2[j];
            }
            PrintPattern(pNtk, i, pat1, bddvar);
            PrintPattern(pNtk, i, pat2, bddvar);
        }

        delete[] arr1;
        delete[] arr2;
        Cudd_RecursiveDeref(dd, w1);
        Cudd_RecursiveDeref(dd, w2);
    }

    // Cleanup
    Cudd_RecursiveDeref(dd, f);
    Cudd_RecursiveDeref(dd, xi);
    Cudd_RecursiveDeref(dd, f0);
    Cudd_RecursiveDeref(dd, f1);

    return 0;
}










// Helper macros for SAT solver literals (assuming MiniSAT-style interface)
#define LitFromVar( Var )         ( (Var) << 1 )
#define LitFromVarSign( Var, Sign ) ( ( (Var) << 1 ) | (Sign) )

// Helper macro to recover variable index from a literal
#define VarFromLit( Lit )         ( (Lit) >> 1 )

// Helper macro to print a literal (using MiniSAT convention: 1 for NOT, 0 for positive)
#define PrintLit( Lit ) Abc_Print(-2, "%s%d ", (Lit) & 1 ? "!" : "", VarFromLit(Lit))

// Helper to print a counterexample (unchanged)
static void Lsv_PrintCounterexample(int k, int i, int nPIs, const std::vector<int>& ce_vals, const char* type)
{
    //Abc_Print(-2,"Counterexample (PO %d, PI %d, %s violation): ", k, i, type);
    for (int t=0; t<nPIs; ++t) {
        if (t==i) {
            Abc_Print(-2,"-");
        } else {
            Abc_Print(-2,"%d", ce_vals[t]);
        }
        Abc_Print(-2,"%s", (t+1<nPIs)?"":"\n");
    }
}

// Helper to extract assignment (unchanged)
static void Lsv_ExtractAssignment(sat_solver * pSat, int nPIs, const std::vector<int>& piVarsA, std::vector<int>& ce_storage)
{
    ce_storage.clear();
    for (int t=0; t<nPIs; ++t) {
        int val = sat_solver_var_value(pSat, piVarsA[t]);
        ce_storage.push_back(val < 0 ? 0 : val);
    }
}

// ---------- main worker (with debug output) ----------
static int Lsv_UnateSat_Run(Abc_Frame_t * pAbc, int k, int i)
{
    Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) return 1;

    // ... (Steps 1 through 3: Cone, AIG, CNF A/B derivation/lifting are assumed correct) ...
    // ... (The code here matches your latest snippet) ...
    
    // 1) 取得 PO 的 driver node
    Abc_Obj_t * pPoObj = Abc_NtkPo(pNtk, k);
    if (!pPoObj) { Abc_Print(-1,"PO %d not found\n", k); return 1; }
    Abc_Obj_t * pRoot = Abc_ObjFanin0(pPoObj);
    if (!pRoot) { Abc_Print(-1,"PO %d has no fanin\n", k); return 1; }

    // 2) 建立 cone, 保持 PI ID (Hint 3 requires the last parameter to be 1)
    Abc_Ntk_t * pCone = Abc_NtkCreateCone(pNtk, pRoot, (char*)"CONE_Y", 1);
    if (!pCone) { Abc_Print(-1,"cannot create cone\n"); return 1; }
    int isInverted = Abc_ObjFaninC0(pPoObj);


    // 3) 轉 AIG
    Aig_Man_t * pAig = Abc_NtkToDar(pCone, 0, 0);
    Abc_NtkDelete(pCone);
    if (!pAig) { Abc_Print(-1,"cannot convert to AIG\n"); return 1; }

    // 4) 產生 CNF A
    Cnf_Dat_t * pCnfA = Cnf_Derive(pAig, 1);
    if (!pCnfA) { Abc_Print(-1,"cannot derive CNF A\n"); Aig_ManStop(pAig); return 1; }

    // 5) 初始化 SAT solver 並加入 CNF A
    sat_solver * pSat = sat_solver_new();
    if (!pSat) { Abc_Print(-1,"cannot create SAT solver\n"); Cnf_DataFree(pCnfA); Aig_ManStop(pAig); return 1; }
    Cnf_DataWriteIntoSolverInt((void*)pSat, pCnfA, 1, 0);

    // 6) 產生 CNF B 並 lift
    Cnf_Dat_t * pCnfB = Cnf_Derive(pAig, 1);
    if (!pCnfB) { Abc_Print(-1,"cannot duplicate CNF B\n"); sat_solver_delete(pSat); Cnf_DataFree(pCnfA); Aig_ManStop(pAig); return 1; }
    Cnf_DataLift(pCnfB, pCnfA->nVars);
    Cnf_DataWriteIntoSolverInt((void*)pSat, pCnfB, 1, 0);
    


    // 7) 對應 AIG PI → CNF 變數
    std::vector<int> piVarsA, piVarsB;
    Aig_Obj_t * pObj;
    int idx;
    // Iterate over AIG CIs (PIs of the cone)
    Aig_ManForEachCi(pAig, pObj, idx) {
        int id = Aig_ObjId(pObj); // AIG CI ID
        int varA = pCnfA->pVarNums[id] ; // CNF A 變數
        int varB = pCnfB->pVarNums[id] ; // CNF B 變數
        piVarsA.push_back(varA);
        piVarsB.push_back(varB);
    }

    int nPIs = (int)piVarsA.size();
    if (i < 0 || i >= nPIs) {
        Abc_Print(-1,"input index out of range: %d (nPIs=%d)\n", i, nPIs);
        sat_solver_delete(pSat); Cnf_DataFree(pCnfA); Cnf_DataFree(pCnfB); Aig_ManStop(pAig); return 1;
    }
    
    for (int t = 0; t < nPIs; ++t) {
        if (t == i) continue;
        int vA = piVarsA[t], vB = piVarsB[t];
        
        int lits1[2] = { LitFromVarSign(vA,1), LitFromVarSign(vB,0) }; // ¬vA ∨ vB 
        int lits2[2] = { LitFromVarSign(vA,0), LitFromVarSign(vB,1) }; // vA ∨ ¬vB


        sat_solver_addclause(pSat, lits1, lits1+2);
        sat_solver_addclause(pSat, lits2, lits2+2);
    }

    // 9) CO 對應 CNF 變數
    Aig_Obj_t * pCo = Aig_ManCo(pAig, 0);
    int varYA = pCnfA->pVarNums[Aig_ObjId(pCo)] ;
    int varYB = pCnfB->pVarNums[Aig_ObjId(pCo)] ;
    
  


    // 10) lambda: SAT solve with assumptions
    // ... (The lambda is defined here using the logic you provided) ...
    auto check_violation = [&](int xA_val,int xB_val,int yA_val,int yB_val)->int{
        int assumptions[4];
        
        assumptions[0] = LitFromVarSign(piVarsA[i], xA_val ? 0 : 1);
        assumptions[1] = LitFromVarSign(piVarsB[i], xB_val ? 0 : 1);

        // Compute the correct root values according to inversion
        int rootY_A_val = isInverted ? (1 - yA_val) : yA_val;
        int rootY_B_val = isInverted ? (1 - yB_val) : yB_val;

        // Apply SAT literals
        assumptions[2] = LitFromVarSign(varYA, rootY_A_val ? 0 : 1);
        assumptions[3] = LitFromVarSign(varYB, rootY_B_val ? 0 : 1);


        
        int res = sat_solver_solve(pSat, assumptions, assumptions+4,0,0,0,0);
        
        return res==1?1:0;
    };
    
    // ... (Steps 11 and 12 remain the same, using the new debugged check_violation) ...
    
    std::vector<int> ce_pos_vio; // Stores assignment that proves POS violation
    std::vector<int> ce_neg_vio; // Stores assignment that proves NEG violation

    // Positive Unate Violation: (x_i=0) -> y=1 AND (x_i=1) -> y=0

    int pos_violation = check_violation(0,1, 1,0); 
    if (pos_violation) {
        Lsv_ExtractAssignment(pSat, nPIs, piVarsA, ce_pos_vio);
    }

    // Negative Unate Violation: (x_i=0) -> y=0 AND (x_i=1) -> y=1

    int neg_violation = check_violation(0,1, 0,1);
    if (neg_violation) {
        Lsv_ExtractAssignment(pSat, nPIs, piVarsA, ce_neg_vio);
    }
    

    const char* result;
    if (!pos_violation && !neg_violation) result = "independent";
    else if (!pos_violation && neg_violation) result = "positive unate";
    else if (pos_violation && !neg_violation) result = "negative unate";
    else result = "binate";

    Abc_Print(-2,"%s\n",result);

    // 12) Output all available counterexamples
    // ... (print_ce lambda and output calls remain the same) ...

    if (pos_violation && neg_violation) {
        Lsv_PrintCounterexample(k, i, nPIs, ce_neg_vio, "Negative Unateness");
        Lsv_PrintCounterexample(k, i, nPIs, ce_pos_vio, "Positive Unateness");
        
    }
    // cleanup
    sat_solver_delete(pSat);
    Cnf_DataFree(pCnfA);
    Cnf_DataFree(pCnfB);
    Aig_ManStop(pAig);

    return 0;
}

// wrapper
int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv)
{
    if (argc != 3) { Abc_Print(-1,"usage: lsv_unate_sat <po index> <pi index>\n"); return 1; }
    int k = atoi(argv[1]);
    int i = atoi(argv[2]);
    return Lsv_UnateSat_Run(pAbc, k, i);
}