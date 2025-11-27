
#include <algorithm>
#include <iostream>
#include <map>
#include <set>
#include <vector>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/extrab/extraBdd.h"

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

static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

/* -------------- */

// };


void Lsv_UnateBDD(Abc_Ntk_t* pNtk, int k, int i) {
    DdManager* dd = (DdManager*)Abc_NtkBuildGlobalBdds(pNtk, 10000000, 0, 1, 0, 0);
    if (dd == NULL) {
        printf("Error: BDD construction failed.\n");
        return;
    }

    // 1. 取得 Output node (yk) 的 BDD
    Abc_Obj_t* pPOk = Abc_NtkPo(pNtk, k);
    DdNode* yk = (DdNode*)Abc_ObjGlobalBdd(pPOk);
    if (yk == NULL) {
        printf("Error: PO %d has no global BDD.\n", k);
        Abc_NtkFreeGlobalBdds(pNtk, 1);
        return;
    }
    Cudd_Ref(yk);

    // 2. 【關鍵修正】正確取得 Input (xi) 對應的 BDD 變數
    // 不要使用 Cudd_bddIthVar(dd, i)，因為 BDD index != PI index
    Abc_Obj_t* pPiObj = Abc_NtkPi(pNtk, i); 
    DdNode* xi = (DdNode*)Abc_ObjGlobalBdd(pPiObj); 
    if (xi == NULL) {
        printf("Error: PI %d has no global BDD.\n", i);
        Cudd_RecursiveDeref(dd, yk);
        Abc_NtkFreeGlobalBdds(pNtk, 1);
        return;
    }
    Cudd_Ref(xi);

    // 3. 計算 Cofactors 和 Unateness 檢查
    DdNode* xi_neg = Cudd_Not(xi);
    Cudd_Ref(xi_neg);

    DdNode* yk_cof_xi = Cudd_Cofactor(dd, yk, xi);
    Cudd_Ref(yk_cof_xi);
    
    DdNode* yk_cof_xi_neg = Cudd_Cofactor(dd, yk, xi_neg);
    Cudd_Ref(yk_cof_xi_neg);

    // A = y_xi AND (NOT y_not_xi) -> 必須由 xi=1 導致的差異
    // (~fxi' + fxi == 1) => f is pos unate on xi <=> fxi' & ~fxi == 0
    DdNode* A = Cudd_bddAnd(dd, Cudd_Not(yk_cof_xi), yk_cof_xi_neg);
    Cudd_Ref(A);
    
    // B = (NOT y_xi) AND y_not_xi -> 必須由 xi=0 導致的差異
    DdNode* B = Cudd_bddAnd(dd, yk_cof_xi, Cudd_Not(yk_cof_xi_neg));
    Cudd_Ref(B);

    // 4. 判斷並輸出結果

    // independent <=> not pos or neg unate <=> (~fxi' + fxi == 1) & (fxi' + ~fxi == 1)
    // <=> A == 0 & B == 0
    if (A == Cudd_ReadLogicZero(dd) && B == Cudd_ReadLogicZero(dd)) {
        printf("independent\n");
    } else if (A == Cudd_ReadLogicZero(dd)) {
        printf("positive unate\n");
    } else if (B == Cudd_ReadLogicZero(dd)) {
        printf("negative unate\n");
    } else {
        printf("binate\n");

        
        // assignments a1, a2
        // Let fa1 = xi, ~fa2 = xi
        // => fxi = 1, fxi' = 0
        // => (fxi & ~fxi') == 1 <=> B == 1
        // a1 = any cube for B

        // Similar for a2,
        // => fxi = 0, fxi' = 1
        // => (~fxi & fxi') == 1 <=> A == 1
        // a2 = any cube for A
        

        int nVars = dd->size; // BDD Manager 中的總變數數量
        int nPis = Abc_NtkPiNum(pNtk);

        // 透過 CUDD 提取 Cube
        // Cube 陣列長度必須為 nVars，因為它根據 BDD 變數索引填值
        char* cubeA = (char*)malloc(sizeof(char) * (nVars + 1)); // +1 for null terminator
        char* cubeB = (char*)malloc(sizeof(char) * (nVars + 1));
        
        // 雖然 PickOneCube 會填滿陣列，但為了安全先清空或填 null
        memset(cubeA, 0, nVars + 1); 
        memset(cubeB, 0, nVars + 1);

        int okA = Cudd_bddPickOneCube(dd, A, cubeA);
        int okB = Cudd_bddPickOneCube(dd, B, cubeB);

        if (!okA || !okB) {
            printf("Error: Failed to pick cube.\n");
        } else {
            // Debug: 如果你想看原始 Cube，可以解除註解
            // printf("Raw cubeA: %s\n", cubeA);

            // 5. 將 BDD Cube 轉換回 PI Pattern
            std::string patA = "";
            std::string patB = "";

            for (int j = 0; j < nPis; ++j) {
                if (j == i) {
                    patA += "-";
                    patB += "-";
                } else {
                    Abc_Obj_t* pPiJ = Abc_NtkPi(pNtk, j);
                    DdNode* bVarJ = (DdNode*)Abc_ObjGlobalBdd(pPiJ);
                    int idx = Cudd_NodeReadIndex(Cudd_Regular(bVarJ));
                    
                    // 直接讀取整數值 (0, 1, 2)
                    int valA = (int)cubeA[idx];
                    int valB = (int)cubeB[idx];

                    // 正確的轉換邏輯：
                    // 只有當數值明確等於 1 時才印 "1"，否則 (0 或 2: don't care) 都印 "0"
                    patA += (valA == 1) ? "1" : "0";
                    patB += (valB == 1) ? "1" : "0";
                }
            }
            std::cout << patB << std::endl;
            std::cout << patA << std::endl;
        }
        free(cubeA);
        free(cubeB);
    }

    // 清理 Reference Count
    Cudd_RecursiveDeref(dd, yk);
    Cudd_RecursiveDeref(dd, xi);
    Cudd_RecursiveDeref(dd, xi_neg);
    Cudd_RecursiveDeref(dd, yk_cof_xi);
    Cudd_RecursiveDeref(dd, yk_cof_xi_neg);
    Cudd_RecursiveDeref(dd, A);
    Cudd_RecursiveDeref(dd, B);

    // 釋放 Global BDDs
    Abc_NtkFreeGlobalBdds(pNtk, 1);
}

int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
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
    Lsv_UnateBDD(pNtk, k, i);
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
