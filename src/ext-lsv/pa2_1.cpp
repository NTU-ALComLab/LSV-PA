#include "base/abc/abc.h"
#include "base/main/main.h"
typedef unsigned long ptrint;
#include "bdd/cudd/cudd.h"

void Lsv_PrintPattern(Abc_Ntk_t* pNtk, Abc_Obj_t* pNode,
                      DdManager* BddMan, DdNode* BddDiff,
                      int targetPiIndex) 
{
    int nVars = Cudd_ReadSize(BddMan);
    int nPis  = Abc_NtkPiNum(pNtk);

    // Pick one cube
    char* cube = new char[nVars];
    if (!Cudd_bddPickOneCube(BddMan, BddDiff, cube)) {
        printf("Error: empty BDD.\n");
        return;
    }

    // Initialize output pattern
    char* pattern = new char[nPis + 1];
    memset(pattern, '-', nPis);
    pattern[nPis] = '\0';

    // Assign 0/1 from local BDD cube back to global PI positions
    int nFanins = Abc_ObjFaninNum(pNode);
    for (int j = 0; j < nFanins; ++j) {
        Abc_Obj_t* pFanin = Abc_ObjFanin(pNode, j);
        int piIndex = Vec_PtrFind(pNtk->vPis, pFanin);

        if (piIndex >= 0 && piIndex < nPis) {
            if (cube[j] == 0) pattern[piIndex] = '0';
            else if (cube[j] == 1) pattern[piIndex] = '1';
        }
    }

    pattern[targetPiIndex] = '-';

    printf("%s\n", pattern);

    delete[] pattern;
    delete[] cube;
}

int pa2_1(Abc_Frame_t* pAbc, int argc, char** argv) {
    // lsv_unate_bdd <k> <i>
    if (argc != 3) {
        Abc_Print(-1, "Usage: lsv_unate_bdd <k> <i>\n");
        return 1;
    }

    int k = atoi(argv[1]);
    int i = atoi(argv[2]); 

    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Empty Network.\n");
        return 1;
    }

    if (!Abc_NtkIsBddLogic(pNtk)) {
        Abc_Print(-1, "Please run 'collapse' first.\n");
        return 1;
    }

    // Po: Output number, Pi: Inpnt number
    if (k< 0 || k >= Abc_NtkPoNum(pNtk)) {
        Abc_Print(-1, "Invalid output index.\n");
        return 1;
    }
    if (i < 0 || i >= Abc_NtkPiNum(pNtk)) {
        Abc_Print(-1, "Invalid input index.\n");
        return 1;
    }

    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);   // 取出第k個 PO
    Abc_Obj_t* pNode = Abc_ObjFanin0(pPo); // 驅動 PO 的節點
    Abc_Obj_t* pPi = Abc_NtkPi(pNtk, i);   // 目標 PI

    // 若 pNode 接到 PI or 是 const
    if (!Abc_ObjIsNode(pNode)) {
        if (pNode == pPi){
            printf("positive unate\n");
        }
        else {
            printf("independent\n");
        }         
        return 0;
    }

    // 尋找 pi 在 bdd中變數的位置
    int bddVarIdx = -1;
    for (int j = 0; j < Abc_ObjFaninNum(pNode); j++) {
        if (Abc_ObjFanin(pNode, j) == pPi) {
            bddVarIdx = j;
            break;
        }
    }

    // pi 不在 Fanin -> independent
    if (bddVarIdx == -1) {
        printf("independent\n");
        return 0;
    }


    DdManager* BddMan = (DdManager*)pNtk->pManFunc;
    DdNode* BddFunc = (DdNode*)pNode->pData; // f ex:f=x1 and x2
    DdNode* BddVar = Cudd_bddIthVar(BddMan, bddVarIdx); // xi

    //f(xi)cofactor
    DdNode* BddPos = Cudd_Cofactor(BddMan, BddFunc, BddVar);       
    Cudd_Ref(BddPos);
    //f(notxi)cofactor
    DdNode* BddNeg = Cudd_Cofactor(BddMan, BddFunc, Cudd_Not(BddVar)); 
    Cudd_Ref(BddNeg);

    // Leq = less or not equal to 
    int isPosUnate = Cudd_bddLeq(BddMan, BddNeg, BddPos); // Neg -> Pos
    int isNegUnate = Cudd_bddLeq(BddMan, BddPos, BddNeg); // Pos -> Neg

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
        // 生成 Binate 的反例
        
        // Pattern 1: (x: 0->1, y: 0->1) => Pos=1 & Neg=0
        DdNode* diff1 = Cudd_bddAnd(BddMan, BddPos, Cudd_Not(BddNeg)); 
        Cudd_Ref(diff1);
        Lsv_PrintPattern(pNtk, pNode, BddMan, diff1, i);
        Cudd_RecursiveDeref(BddMan, diff1);

        // Pattern 2: (x: 0->1, y: 1->0) => Pos=0 & Neg=1
        DdNode* diff2 = Cudd_bddAnd(BddMan, BddNeg, Cudd_Not(BddPos)); 
        Cudd_Ref(diff2);
        Lsv_PrintPattern(pNtk, pNode, BddMan, diff2, i);
        Cudd_RecursiveDeref(BddMan, diff2);
    }

    Cudd_RecursiveDeref(BddMan, BddPos);
    Cudd_RecursiveDeref(BddMan, BddNeg);

    return 0;
}


