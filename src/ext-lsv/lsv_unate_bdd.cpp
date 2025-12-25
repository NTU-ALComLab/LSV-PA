#include <iostream>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <deque>
#include <map>
#include <algorithm>
#include <vector>
#include <string>
#include "bdd/cudd/cuddInt.h"
using namespace std;


int Abc_CommandCheckUnateBDD(Abc_Frame_t *pAbc, int argc, char **argv)
{
    if (argc != 3) {
        Abc_Print(-1, "Usage: lsv_unate_bdd <k> <i>\n");
        return 1;
    }

    int k = atoi(argv[1]);
    int i = atoi(argv[2]);

    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
    if (pNtk == NULL) {
        Abc_Print(-1, "Error: no network loaded.\n");
        return 1;
    }

    // Confirm network type
    printf("Network type = %d\n", pNtk->ntkType);
    printf("Is BDD? %d\n", Abc_NtkIsBddLogic(pNtk));
    printf("Is AIG? %d\n", Abc_NtkIsStrash(pNtk));

    if (!Abc_NtkIsBddLogic(pNtk)) {
        Abc_Print(-1, "Error: run \"collapse\" before lsv_unate_bdd.\n");
        return 1;
    }

    Abc_Ntk_t * pStrash = Abc_NtkStrash(pNtk, 0, 1, 0);
    if (pStrash == NULL) {
        printf("Failed to strash network!\n");
        return 1;
    }
    pNtk = pStrash;

    // Build global BDDs (use the same settings as ABC's print_unate)
    DdManager *dd = (DdManager*)Abc_NtkBuildGlobalBdds(pNtk, 10000000, 1, 1, 0, 0);
    if (dd == NULL) {
        Abc_Print(-1, "Error: Abc_NtkBuildGlobalBdds() returned NULL\n");
        return 1;
    }
    printf("BuildGlobalBdds\n");
    printf("BDD manager created. live nodes = %d\n", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd));

    // Validate k index and get PO
    int nPo = Abc_NtkPoNum(pNtk);
    printf("Number of POs = %d\n", nPo);
    if (k < 0 || k >= nPo) {
        Abc_Print(-1, "Error: output index k=%d out of range (0..%d)\n", k, nPo - 1);
        Abc_NtkFreeGlobalBdds(pNtk, 1);
        return 1;
    }

    Abc_Obj_t *pPo = Abc_NtkPo(pNtk, k);
    if (pPo == NULL) {
        Abc_Print(-1, "Error: Abc_NtkPo returned NULL for k=%d\n", k);
        Abc_NtkFreeGlobalBdds(pNtk, 1);
        return 1;
    }

    // Get BDD pointer attached to the PO (NULL-safe cast)
    void *pv = Abc_ObjGlobalBdd(pPo);
    if (pv == NULL) {
        Abc_Print(-1, "Error: Abc_ObjGlobalBdd returned NULL for PO %d -- BDD not attached\n", k);
        Abc_NtkFreeGlobalBdds(pNtk, 1);
        return 1;
    }
    DdNode *f = (DdNode*) pv;
    if (f == NULL) {                      // paranoid
        Abc_Print(-1, "Error: casted PO BDD pointer is NULL\n");
        Abc_NtkFreeGlobalBdds(pNtk, 1);
        return 1;
    }
    Cudd_Ref(f);

    // Validate variable index and manager
    int nVars = Cudd_ReadSize(dd); // number of BDD vars in manager
    printf("BDD manager size = %d vars\n", nVars);
    if (i < 0 || i >= nVars) {
        Abc_Print(-1, "Error: input var index i=%d out of range (0..%d)\n", i, nVars - 1);
        Cudd_RecursiveDeref(dd, f);
        Abc_NtkFreeGlobalBdds(pNtk, 1);
        return 1;
    }

    // Now operate on cofactors
    DdNode *var  = Cudd_bddIthVar(dd, i);
    if (var == NULL) {
        Abc_Print(-1, "Error: Cudd_bddIthVar returned NULL for i=%d\n", i);
        Cudd_RecursiveDeref(dd, f);
        Abc_NtkFreeGlobalBdds(pNtk, 1);
        return 1;
    }
    DdNode *nvar = Cudd_Not(var);

    DdNode *f0 = Cudd_Cofactor(dd, f, nvar);  Cudd_Ref(f0);
    DdNode *f1 = Cudd_Cofactor(dd, f, var);   Cudd_Ref(f1);

    if (f0 == f1) {
        printf("independent\n");
        Cudd_RecursiveDeref(dd, f0);
        Cudd_RecursiveDeref(dd, f1);
        Cudd_RecursiveDeref(dd, f);
        Abc_NtkFreeGlobalBdds(pNtk, 1);
        return 0;
    }

    DdNode *pos = Cudd_bddAnd(dd, f0, Cudd_Not(f1));  Cudd_Ref(pos);
    int isPosUnate = (pos == Cudd_ReadLogicZero(dd));
    Cudd_RecursiveDeref(dd, pos);

    DdNode *neg = Cudd_bddAnd(dd, f1, Cudd_Not(f0));  Cudd_Ref(neg);
    int isNegUnate = (neg == Cudd_ReadLogicZero(dd));
    Cudd_RecursiveDeref(dd, neg);

    if (isPosUnate)
        printf("positive unate\n");
    else if (isNegUnate)
        printf("negative unate\n");
    else
        printf("binate\n");
        int nvars = Cudd_ReadSize(dd);
        char* cube_str = new char[nvars + 1];
        DdNode* g = Cudd_bddAnd(dd, f1, Cudd_Not(f0));
        int cube = Cudd_bddPickOneCube(dd, g, cube_str);
        for (int j = 0; j < nvars; j++) {
            if(i == j){
                printf("- ");
            }
            else if(cube_str[j] == 2){
                printf("0 ");
            }
            else{
                printf("%d ", cube_str[j]);
            }
        }
        printf("\n");

        g = Cudd_bddAnd(dd, f0, Cudd_Not(f1));
        cube = Cudd_bddPickOneCube(dd, g, cube_str);
        //offset = 0;
        for (int j = 0; j < nvars; j++) {
            if(i == j){
                printf("- ");
            }
            else if(cube_str[j] == 2){
                printf("0 ");
            }
            else{
                printf("%d ", cube_str[j]);
            }
        }
        printf("\n");


    // cleanup
    Cudd_RecursiveDeref(dd, f0);
    Cudd_RecursiveDeref(dd, f1);
    Cudd_RecursiveDeref(dd, f);
    Abc_NtkFreeGlobalBdds(pNtk, 1);

    return 0;
}