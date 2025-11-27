
#include <algorithm>
#include <iostream>
#include <set>
#include <vector>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/extrab/extraBdd.h"
#include "sat/cnf/cnf.h"

extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

/*
1 [Unateness Checking with BDD]

  Given a circuit C in BDD, a primary output yk , and a primary input xi, write a
procedure in ABC to check whether the function of yk is binate, positive unate,
negative unate in xi, or independent of xi. If the function of yk is binate in xi,
show that it is indeed binate by giving some input patterns.
  Integrate this procedure into ABC (under src/ext-lsv/), so that after read-
ing in a circuit (by command “read”) and transforming it into BDD (by com-
mand “collapse”), running the command “lsv unate bdd” would invoke your
code. The command should have the following format.

    lsv unate bdd <k> <i>

where k is a primary output index starting from 0, and i is a primary input
index starting from 0.
  If the function of yk is positive unate, negative unate in xi, or is independent
of xi, print one of the following three lines:

    positive unate
    negative unate
    independent

  Otherwise, print “binate” and show that it is binate in the following format.
binate

    <pattern 1>
    <pattern 2>

  Patterns 1 and 2 are primary input assignments where all the primary inputs,
except xi, are assigned as 0 or 1. For xi, please use ”-” to represent its value.
Cofactoring the function of yk with respect to the cube of Pattern 1 (respectively,
Pattern 2) produces a new function equal to xi (respectively,¬xi).
  For example, consider the checking for function y0 = (x0 ⊕x1)∨x2 on variable
x0. The command should output the following information:

    abc 01> lsv_unate_bdd 0 2
    positive unate
    abc 02> lsv_unate_bdd 0 0
    binate
    -00
    -10
*/

using namespace std;
namespace {

static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

/* -------------- */
void Lsv_UnateSat(Abc_Ntk_t* pNtk, int k, int i) {
    // 1. Build cone of y_k
    Abc_Obj_t* pPo   = Abc_NtkPo(pNtk, k);                     // kth PO
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);                     // its driver
    Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, pRoot,
                                         Abc_ObjName(pRoot), 1);
    if (pCone == NULL) {
        printf("Error: Abc_NtkCreateCone failed.\n");
        return;
    }

    // 2. Convert to AIG
    Aig_Man_t* pMan = Abc_NtkToDar(pCone, 0, 0);
    if (pMan == NULL) {                     // <-- BUGFIX: check pMan, not pCone
        printf("Error: Abc_NtkToDar failed.\n");
        Abc_NtkDelete(pCone);
        return;
    }

    // 3. Derive CNF for one copy
    Cnf_Dat_t* pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    if (pCnf == NULL) {
        printf("Error: Cnf_Derive failed.\n");
        Aig_ManStop(pMan);
        Abc_NtkDelete(pCone);
        return;
    }

    int nCnfVars = pCnf->nVars;
    int nPis     = Aig_ManCiNum(pMan);

    // ---------- FIX #1: remember var IDs of copy A before lifting ----------
    int nObjMax = Aig_ManObjNumMax(pMan);
    int* pVarA  = ABC_CALLOC(int, nObjMax);
    for (int id = 0; id < nObjMax; ++id)
        pVarA[id] = pCnf->pVarNums[id];     // may be -1 for non-used objects
    // -----------------------------------------------------------------------

    // 4. SAT solver and both copies of CNF
    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars(pSat, 2 * nCnfVars);

    // first copy (A): original indices
    Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);

    // second copy (B): lifted by nCnfVars
    Cnf_DataLift(pCnf, nCnfVars);
    Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
    // after this, pCnf->pVarNums[...] are the variable numbers of copy B

    // 5. Constrain all x_j (j != i) to be equal in A and B
    for (int j = 0; j < nPis; ++j) {
        if (j == i) continue;   // skip x_i

        Aig_Obj_t* pObjPi = Aig_ManCi(pMan, j);
        int id   = pObjPi->Id;
        int varA = pVarA[id];               // copy A
        int varB = pCnf->pVarNums[id];      // copy B (already lifted)

        if (varA < 0 || varB < 0) continue; // safety, should not happen

        lit Lits[2];

        // (¬varA + varB)
        Lits[0] = toLitCond(varA, 1);
        Lits[1] = toLitCond(varB, 0);
        sat_solver_addclause(pSat, Lits, Lits + 2);

        // (¬varB + varA)
        Lits[0] = toLitCond(varA, 0);
        Lits[1] = toLitCond(varB, 1);
        sat_solver_addclause(pSat, Lits, Lits + 2);
    }

    // 6. Get variables for x_i in both copies
    Aig_Obj_t* pObjXi = Aig_ManCi(pMan, i);
    int varXi_A = pVarA[pObjXi->Id];
    int varXi_B = pCnf->pVarNums[pObjXi->Id];

    // 7. Get output variable y in both copies
    Aig_Obj_t* pCo   = Aig_ManCo(pMan, 0);
    Aig_Obj_t* pOut  = Aig_ObjFanin0(pCo);
    int varY_A       = pVarA[pOut->Id];
    int varY_B       = pCnf->pVarNums[pOut->Id];

    // If the output has no CNF var (constant), it's independent of x_i
    if (varY_A < 0 || varY_B < 0) {
        printf("independent\n");
        sat_solver_delete(pSat);
        Cnf_DataFree(pCnf);
        Aig_ManStop(pMan);
        Abc_NtkDelete(pCone);
        ABC_FREE(pVarA);
        return;
    }

    // optional: adjust for PO polarity
    int isInv = Abc_ObjFaninC0(pPo) ^ Aig_ObjFaninC0(pCo);
    lit litY_A = toLitCond(varY_A, isInv);
    lit litY_B = toLitCond(varY_B, isInv);

    // 8. SAT checks
    lit assumptions[4];

    // ---------- check counterexample to **positive** unateness ----------
    // xA = 0, xB = 1, yA = 1, yB = 0
    assumptions[0] = toLitCond(varXi_A, 1);   // x_i(A) = 0
    assumptions[1] = toLitCond(varXi_B, 0);   // x_i(B) = 1
    assumptions[2] = litY_A;                  // yA = 1
    assumptions[3] = lit_neg(litY_B);         // yB = 0
    int statusPossibleNegUnate = sat_solver_solve(pSat, assumptions, assumptions + 4,
                                        0, 0, 0, 0);

    std::vector<int> pattern2; // for yA=1, yB=0 (negative behaviour)
    if (statusPossibleNegUnate == l_True) {
        for (int j = 0; j < nPis; ++j) {
            if (j == i) continue;
            Aig_Obj_t* pObj = Aig_ManCi(pMan, j);
            int var = pVarA[pObj->Id];       // either copy is fine, they’re equal
            pattern2.push_back(sat_solver_var_value(pSat, var));
        }
    }

    // ---------- check counterexample to **negative** unateness ----------
    // xA = 0, xB = 1, yA = 0, yB = 1
    assumptions[2] = lit_neg(litY_A);         // yA = 0
    assumptions[3] = litY_B;                  // yB = 1
    int statusPossiblePosUnate = sat_solver_solve(pSat, assumptions, assumptions + 4,
                                        0, 0, 0, 0);

    std::vector<int> pattern1; // for yA=0, yB=1 (positive behaviour)
    if (statusPossiblePosUnate == l_True) {
        for (int j = 0; j < nPis; ++j) {
            if (j == i) continue;
            Aig_Obj_t* pObj = Aig_ManCi(pMan, j);
            int var = pVarA[pObj->Id];
            pattern1.push_back(sat_solver_var_value(pSat, var));
        }
    }

    // 9. Classify
    if (statusPossibleNegUnate == l_False && statusPossiblePosUnate == l_False) {
        printf("independent\n");
    } else if (statusPossibleNegUnate == l_False && statusPossiblePosUnate == l_True) {
        printf("positive unate\n");
    } else if (statusPossibleNegUnate == l_True && statusPossiblePosUnate == l_False) {
        printf("negative unate\n");
    } else {
        printf("binate\n");

        // Pattern 1: yA=0, yB=1
        for (int j = 0, pIdx = 0; j < nPis; ++j) {
            if (j == i) printf("-");
            else        printf("%d", pattern1[pIdx++]);
        }
        printf("\n");

        // Pattern 2: yA=1, yB=0
        for (int j = 0, pIdx = 0; j < nPis; ++j) {
            if (j == i) printf("-");
            else        printf("%d", pattern2[pIdx++]);
        }
        printf("\n");
    }

    // 10. cleanup
    sat_solver_delete(pSat);
    Cnf_DataFree(pCnf);
    Aig_ManStop(pMan);
    Abc_NtkDelete(pCone);
    ABC_FREE(pVarA);
}

// void Lsv_UnateSat(Abc_Ntk_t* pNtk, int k, int i) {
//     Abc_Obj_t* pPok = Abc_NtkPo(pNtk, k);   // get kth PO
//     Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPok), Abc_ObjName(Abc_ObjFanin0(pPok)), 1);     // create cone of kth PO
//     if (pCone == NULL) {
//         printf("Error: Abc_NtkCreateCone failed.\n");
//         return;
//     }

//     // Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters)
//     Aig_Man_t* pMan = Abc_NtkToDar(pCone, 0, 0);
//     if (pCone == NULL) {
//         printf("Error: Abc_NtkToDar failed.\n");
//         return;
//     }

//     Cnf_Dat_t* pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));     // Aig_ManCoNum(pMan) = 1 for this case
//     if (pCnf == NULL) {
//         printf("Error: Cnf_Derive failed.\n");
//         return;
//     }

//     // initialize sat solver
//     sat_solver* pSat = sat_solver_new();
//     int nCnfVars = pCnf->nVars;
//     sat_solver_setnvars(pSat, 2 * nCnfVars);

//     // add the CNF to the SAT solver
//     Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);

//     cout << nCnfVars << endl;
//     cout << pSat->nVarUsed << endl;
//     // shift variable
//     Cnf_DataLift(pCnf, nCnfVars);
//     Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
//     cout << "!!!!!!!";
//     int nPis = Aig_ManCiNum(pMan);
//     for (int j = 0; j < nPis; j++)
//     {
//         if (j == i) continue;   // skip target variable xi

//         Aig_Obj_t* pObjPi = Aig_ManCi(pMan, j);
//         int varA = pCnf->pVarNums[pObjPi->Id];
//         int varB = varA + nCnfVars;

//         // constraint (varA == varB)
//         // varA -> varB & varB -> varA
//         // (¬VarA + varB) & (¬VarB + VarA) add these 2 clauses
//         // sat_solver_add_const(pSat, varA, varB);

//         lit Lits[2];
//         // toLitCond(int var, int c), var: 變數編號, c (Condition): 是否取反 
//         // c == 0: 回傳正向 Literal（代表 x）
//         // c == 1: 回傳反向 Literal（代表 ¬x）

//         // (¬VarA + varB)
//         Lits[0] = toLitCond(varA, 1);
//         Lits[1] = toLitCond(varB, 0);
//         sat_solver_addclause(pSat, Lits, Lits + 2);
        
//         // (¬VarB + VarA)
//         Lits[0] = toLitCond(varA, 0);
//         Lits[1] = toLitCond(varB, 1);
//         sat_solver_addclause(pSat, Lits, Lits + 2);
//     }
    
//     // 準備變數與 Literals
//     // 取得 x_i 的變數
//     Aig_Obj_t* pObjXi = Aig_ManCi(pMan, i);
//     int varXi_A = pCnf->pVarNums[pObjXi->Id];
//     int varXi_B = varXi_A + nCnfVars;

//     // 取得 Output 的變數 (Driver of PO)
//     // AIG 的 output 是 CO (Combinational Output)
//     Aig_Obj_t* pObjCo = Aig_ManCo(pMan, 0); 
//     Aig_Obj_t* pObjOut = Aig_ObjFanin0(pObjCo);
//     int varY_A = pCnf->pVarNums[pObjOut->Id];
//     if (varY_A == -1) {
//         printf("independent\n");
//         sat_solver_delete(pSat);
//         Cnf_DataFree(pCnf);
//         Aig_ManStop(pMan);
//         Abc_NtkDelete(pCone);
//         return;
//     } 
//     int varY_B = varY_A + nCnfVars;
    
//     int isInv = Abc_ObjFaninC0(pPok) ^ Aig_ObjFaninC0(pObjCo);
    
//     // 帶入 isInv 作為 toLitCond 的第二個參數
//     lit litY_A = toLitCond(varY_A, isInv);
//     lit litY_B = toLitCond(varY_B, isInv);

//     // 9. Sat solving
//     // Assumption Array
//     // Assumption 的作用是「暫時性的假設」。它告訴 Solver：
//     // 「請在這個特定的 sat_solver_solve 呼叫中，幫我看看如果 yA=1,yB=0 會發生什麼事？
//     // 如果找不到解就回傳 UNSAT，但不要把這個限制永久寫入資料庫。」

//     lit assumptions[4];
//     assumptions[0] = toLitCond(varXi_A, 1); // x_i = 0 in A => xi negative cofactor for A
//     assumptions[1] = toLitCond(varXi_B, 0); // x_i = 1 in B => xi positive cofactor for B

//     // if we can find y_A = 1, y_B = 0 (i.e. solver return sat) => we can find assignment for y_A include y_B
//     // 假設: y_A = 1, y_B = 0
//     assumptions[2] = litY_A;            // y_A = 1
//     assumptions[3] = lit_neg(litY_B);   // y_B = 0
//     cout << "`````";
//     int statusPossibleNegUnate = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
//     cout << "ssssss";
//     // 如果 SAT，代表找到了 "負向變化" 的反例 (Pattern 2)
//     std::vector<int> pattern2; 
//     if (statusPossibleNegUnate == l_True) {
//         for (int j = 0; j < nPis; j++) {
//              if (j == i) continue;
//              Aig_Obj_t* pObj = Aig_ManCi(pMan, j);
//              int var = pCnf->pVarNums[pObj->Id];
//              pattern2.push_back(sat_solver_var_value(pSat, var));
//         }
//     }

//     // if we can find y_A = 0, y_B = 1 (i.e. solver return sat) => => we can find assignment for y_B include y_A
//     // 假設: y_A = 0, y_B = 1 
//     assumptions[2] = lit_neg(litY_A);   // y_A = 0
//     assumptions[3] = litY_B;            // y_B = 1

//     int statusPossiblePosUnate = sat_solver_solve(pSat, assumptions, assumptions + 4, 0, 0, 0, 0);
//     // 如果 SAT，代表找到了 "正向變化" 的反例 (Pattern 1)
//     std::vector<int> pattern1;
//     if (statusPossiblePosUnate == l_True) {
//         for (int j = 0; j < nPis; j++) {
//              if (j == i) continue;
//              Aig_Obj_t* pObj = Aig_ManCi(pMan, j);
//              int var = pCnf->pVarNums[pObj->Id];
//              pattern1.push_back(sat_solver_var_value(pSat, var));
//         }
//     }

//     // 10. 判斷並輸出結果
//     if (statusPossibleNegUnate == l_False && statusPossiblePosUnate == l_False) {
//         printf("independent\n");
//     } else if (statusPossibleNegUnate == l_False && statusPossiblePosUnate == l_True) {
//         printf("positive unate\n");
//     } else if (statusPossibleNegUnate == l_True && statusPossiblePosUnate == l_False) {
//         printf("negative unate\n");
//     } else {
//         // 兩種行為都有
//         printf("binate\n");
        
//         // Print Pattern 1 (from Positive Behavior check)
//         for (int j = 0, pIdx = 0; j < nPis; j++) {
//             if (j == i) printf("-");
//             else printf("%d", pattern1[pIdx++]);
//         }
//         printf("\n");

//         // Print Pattern 2 (from Negative Behavior check)
//         for (int j = 0, pIdx = 0; j < nPis; j++) {
//             if (j == i) printf("-");
//             else printf("%d", pattern2[pIdx++]);
//         }
//         printf("\n");
//     }

//     // delete
//     sat_solver_delete(pSat);
//     Cnf_DataFree(pCnf);
//     Aig_ManStop(pMan);
//     Abc_NtkDelete(pCone);
// }

int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);  // get current BDD network

    int c;
    int k, i;

    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }
    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "This command works only for AIGs (run \"strash\").\n");
        return 1;
    }

    k = (int)atof(argv[1]);
    i = (int)atof(argv[2]);
    Lsv_UnateSat(pNtk, k, i);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_printmocut [-h] <k> <i>\n");
    Abc_Print(-2, "\t        prints the K-L multi-output cut of the network\n");
    Abc_Print(-2, "\t<k>   : k is a primary output index starting from 0\n");
    Abc_Print(-2, "\t<i>   : i is a primary input index starting from 0\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
}  // namespace

/*
k is a primary output index starting from 0, and i is a primary input
index starting from 0*/
