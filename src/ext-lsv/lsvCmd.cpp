#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include <map>
#include <set>
#include <algorithm>
extern "C"{
  Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}
using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCuts(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocuts", Lsv_CommandPrintMoCuts, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

void Lsv_NtkPrintMoCuts(Abc_Ntk_t* pNtk, int k, int l)
{
    Abc_Obj_t* pObj;
    int i;
    map<set<int>, set<int>> cutmap;
    Abc_NtkForEachObj(pNtk, pObj, i) {
        if(Abc_ObjIsPo(pObj)) continue;
        pObj->pData = new set<set<int>>();
        set<set<int>>& cutset = *(set<set<int>>*)pObj->pData;
        cutset.insert({Abc_ObjId(pObj)});
        Abc_Obj_t* pFanin;
        int j;
        void * cutset0 = NULL, * cutset1 = NULL;
        Abc_ObjForEachFanin(pObj, pFanin, j) {
            if (j == 0) cutset0 = pFanin->pData;
            else cutset1 = pFanin->pData;
        }
        if(cutset0 == NULL || cutset1 == NULL) continue;
        for(auto s0 : *(set<set<int>>*)cutset0) {
            for(auto s1 : *(set<set<int>>*)cutset1) {
                set<int> newset;
                set_union(s0.begin(), s0.end(), s1.begin(), s1.end(), inserter(newset, newset.begin()));
                if ((int)newset.size() <= k) {
                    cutset.insert(newset);
                    cutmap[newset].insert(Abc_ObjId(pObj));
                }
            }
        }
    }
    for (auto it = cutmap.begin(); it != cutmap.end(); it++) {
        if ((int)it->first.size() <= k && (int)it->second.size() >= l) {
            for (auto idit = it->first.begin(); idit != it->first.end(); idit++) {
                printf("%d ", *idit);
            }
            printf(":");
            for (auto idit = it->second.begin(); idit != it->second.end(); idit++) {
                printf(" %d", *idit);
            }
            printf("\n");
        }
    }
}

int Lsv_CommandPrintMoCuts(Abc_Frame_t* pAbc, int argc, char** argv)
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (argc < 3) goto usage;
    Lsv_NtkPrintMoCuts(pNtk, atoi(argv[1]), atoi(argv[2]));
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_mo_cuts [-h] <k> <l>\n");
    return 1;
}

void Lsv_NtkUnateBdd(Abc_Ntk_t* pNtk, int k, int l)
{
    int nPis = Abc_NtkPiNum(pNtk);
    int nPos = Abc_NtkPoNum(pNtk);

    if (k < 0 || k >= nPos) {
        Abc_Print(-1, "PO index %d out of range.\n", k);
        return;
    }
    if (l < 0 || l >= nPis) {
        Abc_Print(-1, "PI index %d out of range.\n", l);
        return;
    }
    DdManager* dd = (DdManager *)pNtk->pManFunc;
    if (!dd) {
        Abc_Print(-1, "Error: BDD manager is NULL. Did you run 'collapse'?\n");
        return;
    }
    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);
    DdNode* f = (DdNode *)pRoot->pData;

    if (!f) {
        Abc_Print(-1, "Error: PO %d does not have a BDD.\n", k);
        return;
    }

    Cudd_Ref(f);

    char** bdd2name_arr = (char**)Abc_NodeGetFaninNames(pRoot)->pArray;
    const int bdd_num = Abc_ObjFaninNum(pRoot);
    int bdd_index[nPis] = {-1};

    for(int j=0; j<nPis; ++j){
        for(int i=0; i<bdd_num; ++i){
            if(strcmp(bdd2name_arr[i], Abc_ObjName(Abc_NtkPi(pNtk, j)))==0){
                bdd_index[j] = i;
                break;
            }
        }
    }
    DdNode* var = Cudd_bddIthVar(dd, bdd_index[l]);
    Cudd_Ref(var);

    DdNode* f1 = Cudd_Cofactor(dd, f, var);
    Cudd_Ref(f1);

    DdNode* f0 = Cudd_Cofactor(dd, f, Cudd_Not(var));
    Cudd_Ref(f0);

    if (f0 == f1) {
        printf("independent\n");

        Cudd_RecursiveDeref(dd, f);
        Cudd_RecursiveDeref(dd, var);
        Cudd_RecursiveDeref(dd, f0);
        Cudd_RecursiveDeref(dd, f1);
        return;
    }

    DdNode* imp01 = Cudd_bddOr(dd, Cudd_Not(f0), f1);
    Cudd_Ref(imp01);

    if (imp01 == Cudd_ReadOne(dd)) {
        printf("positive unate\n");

        Cudd_RecursiveDeref(dd, imp01);
        Cudd_RecursiveDeref(dd, f);
        Cudd_RecursiveDeref(dd, var);
        Cudd_RecursiveDeref(dd, f0);
        Cudd_RecursiveDeref(dd, f1);
        return;
    }

    Cudd_RecursiveDeref(dd, imp01);

    DdNode* imp10 = Cudd_bddOr(dd, Cudd_Not(f1), f0);
    Cudd_Ref(imp10);

    if (imp10 == Cudd_ReadOne(dd)) {
        printf("negative unate\n");

        Cudd_RecursiveDeref(dd, imp10);
        Cudd_RecursiveDeref(dd, f);
        Cudd_RecursiveDeref(dd, var);
        Cudd_RecursiveDeref(dd, f0);
        Cudd_RecursiveDeref(dd, f1);
        return;
    }

    Cudd_RecursiveDeref(dd, imp10);

    printf("binate\n");

    DdNode* t1 = Cudd_bddAnd(dd, f1, Cudd_Not(f0));
    Cudd_Ref(t1);

    DdNode* t2 = Cudd_bddAnd(dd, f0, Cudd_Not(f1));
    Cudd_Ref(t2);

    int nVars = dd->size;

    char* cube1 = (char*)malloc(sizeof(char) * (nVars + 1));
    cube1[nVars] = '\0';
    Cudd_bddPickOneCube(dd, t1, cube1);

    char* cube2 = (char*)malloc(sizeof(char) * (nVars + 1));
    cube2[nVars] = '\0';
    Cudd_bddPickOneCube(dd, t2, cube2);
   
    for (int v = 0; v < nPis; v++) {
        if(v == l) printf("-");
        else if(bdd_index[v] != -1) printf("%c", cube1[bdd_index[v]] == 2 ? '0' : cube1[bdd_index[v]] + '0');
    }
    printf("\n");

    for (int v = 0; v < nPis; v++) {
        if(v == l) printf("-");
        else if(bdd_index[v] != -1) printf("%c", cube2[bdd_index[v]] == 2 ? '0' : cube2[bdd_index[v]] + '0');
    }
    printf("\n");

    Cudd_RecursiveDeref(dd, t1);
    Cudd_RecursiveDeref(dd, t2);
    Cudd_RecursiveDeref(dd, f);
    Cudd_RecursiveDeref(dd, var);
    Cudd_RecursiveDeref(dd, f0);
    Cudd_RecursiveDeref(dd, f1);
}

int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (argc < 3) goto usage;
  Lsv_NtkUnateBdd(pNtk, atoi(argv[1]), atoi(argv[2]));
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_unate_bdd <k> <l>\n");
  return 1;
}

void Lsv_NtkUnateSat(Abc_Ntk_t* pNtk, int k, int l)
{
    int nPis = Abc_NtkPiNum(pNtk);
    int nPos = Abc_NtkPoNum(pNtk);

    if (k < 0 || k >= nPos) {
        Abc_Print(-1, "PO index %d out of range.\n", k);
        return;
    }
    if (l < 0 || l >= nPis) {
        Abc_Print(-1, "PI index %d out of range.\n", l);
        return;
    }

    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
    Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 1);
    Aig_Man_t* pAig = Abc_NtkToDar(pCone, 0, 1);
    sat_solver* pSat = sat_solver_new();
    Cnf_Dat_t* pCnf = Cnf_Derive(pAig, 1);
    pSat = (sat_solver *)Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
    Cnf_DataLift(pCnf, pCnf->nVars);
    pSat = (sat_solver *)Cnf_DataWriteIntoSolverInt(pSat, pCnf, 2, 0);
    Cnf_DataLift(pCnf, -1*pCnf->nVars);

    int pLit[1];
    Aig_Obj_t* pObj; int iObj;
    Aig_ManForEachCi(pAig, pObj, iObj){
        if(iObj==l){
            pLit[0] = toLitCond(pCnf->pVarNums[pObj->Id], 1);
            sat_solver_addclause(pSat, pLit, pLit+1);
            pLit[0] = toLitCond(pCnf->pVarNums[pObj->Id]+pCnf->nVars, 0);
            sat_solver_addclause(pSat, pLit, pLit+1);
            continue;
        }
        sat_solver_add_buffer(pSat, pCnf->pVarNums[pObj->Id], pCnf->pVarNums[pObj->Id]+pCnf->nVars, 0);
    }

    Aig_Obj_t* pRoot = Aig_ObjFanin0(Aig_ManCo(pAig, 0));
    
    int assump[2];
    int nPi = Aig_ManCiNum(pAig);
    char* cube1 = (char*)malloc(sizeof(char) * (nPi + 1));
    cube1[nPi] = '\0';
    char* cube2 = (char*)malloc(sizeof(char) * (nPi + 1));
    cube2[nPi] = '\0';
    assump[0] = toLitCond(pCnf->pVarNums[pRoot->Id], 0);
    assump[1] = toLitCond(pCnf->pVarNums[pRoot->Id]+pCnf->nVars, 1);
    int status_pos = sat_solver_solve(pSat, assump, assump+2, 0,0,0,0);
    Aig_ManForEachCi(pAig, pObj, iObj){
        if(iObj==l) cube1[iObj] = '-';
        else cube1[iObj] = sat_solver_var_value(pSat, pCnf->pVarNums[pObj->Id]) + '0';
    }
    assump[0] = toLitCond(pCnf->pVarNums[pRoot->Id], 1);
    assump[1] = toLitCond(pCnf->pVarNums[pRoot->Id]+pCnf->nVars, 0);
    int status_neg = sat_solver_solve(pSat, assump, assump+2, 0,0,0,0);
    Aig_ManForEachCi(pAig, pObj, iObj){
        if(iObj==l) cube2[iObj] = '-';
        else cube2[iObj] = sat_solver_var_value(pSat, pCnf->pVarNums[pObj->Id]+pCnf->nVars) + '0';
    }
    if(status_pos == l_Undef || status_neg == l_Undef){
        Abc_Print(-1, "SAT solver returns undefined.\n");
        return;
    }
    else if(status_pos == l_True && status_neg == l_True){
        printf("binate\n");
        printf("%s\n", cube1);
        printf("%s\n", cube2);
    }
    else if(status_pos == l_True && status_neg == l_False){
        printf("positive unate\n");
    }
    else if(status_pos == l_False && status_neg == l_True){
        printf("negative unate\n");
    }
    else{
        printf("independent\n");
    }
}

int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (argc < 3) goto usage;
  Lsv_NtkUnateSat(pNtk, atoi(argv[1]), atoi(argv[2]));
  return 0;
usage:
  Abc_Print(-2, "usage: lsv_unate_sat <k> <l>\n");
  return 1;
}