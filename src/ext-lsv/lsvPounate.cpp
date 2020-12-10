#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "opt/dar/dar.h"
#include "sat/bsat/satSolver2.h"
#include "sat/satoko/satoko.h"
#include <stdio.h>
#include <vector>
#include <map>
#include <unordered_map>

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
static int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv);

void init_pounate(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPounate, 0);
}

void destroy_pounate(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t pounate_frame_initializer = {init_pounate, destroy_pounate};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&pounate_frame_initializer); } 
} lsvPackage_pounate_RegistrationManager;

void Abc_PrintPounate();

int add_literal(Cnf_Dat_t* pCnf, Vec_Ptr_t* p, int i, int sign) {
    Aig_Obj_t* tmpObj = (Aig_Obj_t*)Vec_PtrEntry(p, i);
    int Lit;
    Lit = toLitCond( pCnf->pVarNums[tmpObj->Id], 0);
    if (!sign) {
        Lit = lit_neg(Lit);
    }
    return Lit;
}

int Solving(Cnf_Dat_t* pCnf, Cnf_Dat_t* nCnf, sat_solver* pSat, int nCis, int i, int j, int pos) {
    lit Lit;
    lit Lits[nCis+3];
    int num = 0;
    Lits[num++] = add_literal(pCnf, pCnf->pMan->vCos, i, 1);
    Lits[num++] = add_literal(nCnf, nCnf->pMan->vCos, i, 0);
    for (int k = 0; k < nCis; k++) {
        if (k == j) {
            Lits[num++] = add_literal(pCnf, pCnf->pMan->vCis, k, !pos);
            Lits[num++] = add_literal(nCnf, nCnf->pMan->vCis, k, pos);
        } else {
            int v1 = k+pCnf->nVars*2+1;
            Lit = toLitCond( v1, 0);
            Lits[num++] = Lit;
        }
    }

    return sat_solver_solve( pSat, Lits, Lits+nCis+3, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
}

void Abc_PrintPounate(Abc_Ntk_t* pNtk, Abc_Ntk_t* pOrigin, int reverse) {

    assert( Abc_NtkLatchNum(pNtk) == 0);
    Abc_Obj_t* pObj;
    std::map<int, std::string> Names;
    std::unordered_map<std::string, int> mark;
    // the CNF derive and solve part
    Cnf_Dat_t* pCnf; // positive Aig CNF
    Cnf_Dat_t* nCnf; // negative Aig CNF 
    Aig_Man_t* pMan; // the aig manager 
    // get the Aig manager
    pMan = Abc_NtkToDar(pNtk, 0, 0);
    pMan->pData = NULL;

    pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    nCnf = Cnf_DataDup(pCnf); // duplicate the negative AIG CNF
    Cnf_DataLift( nCnf, pCnf->nVars);

    sat_solver* pSat;
    pSat = (sat_solver*)Cnf_DataWriteIntoSolver(pCnf, 1, 0);
    int resCis = Vec_PtrSize(pCnf->pMan->vCis);
    sat_solver_setnvars( pSat, nCnf->nVars * 2 + resCis);
    int i = 0;
    for (i = 0; i < nCnf->nClauses; i++ ) {
        if ( !sat_solver_addclause( pSat, nCnf->pClauses[i], nCnf->pClauses[i+1] ) ){
            sat_solver_delete( pSat );
            return ;
        }
    } 
    Aig_Obj_t* tmpObj, *tmpObj2;
    for (i = 0; i < resCis; i++) {
        tmpObj = (Aig_Obj_t*)Vec_PtrEntry(pCnf->pMan->vCis, i);
        tmpObj2 = (Aig_Obj_t*)Vec_PtrEntry(nCnf->pMan->vCis, i);
        int v1 = pCnf->pVarNums[tmpObj->Id];
        int v2 = nCnf->pVarNums[tmpObj2->Id];
        int v3 = i+pCnf->nVars*2+1;
        sat_solver_add_buffer_enable(pSat, v1, v2, v3, 0);
    }
    sat_solver_simplify(pSat);

    std::vector<std::string> outputNate[3];
    char nate[3][16] = {"+unate", "-unate", "binate"};

    Abc_NtkForEachCi( pOrigin, pObj, i) { 
        std::string tmp  = Abc_ObjName(pObj);
        Names[pObj->Id] = tmp;
    }
    assert(pNtk);
    Abc_NtkForEachPo( pNtk, pObj, i ) {                                      
        int j;
        assert( Vec_PtrSize(pCnf->pMan->vCis) == Vec_PtrSize(nCnf->pMan->vCis));
        // solving part
        Abc_Obj_t* pCi;
        for (j = 0; j < resCis; j++) {
            pCi = Abc_NtkCi(pNtk, j);
            std::string tmp  = Abc_ObjName(pCi);
            mark[tmp] = 1;
        }
        j = 0;
        for (auto name: Names) {
            if (mark.find(name.second) == mark.end()) {
                outputNate[0].push_back(name.second); 
                outputNate[1].push_back(name.second); 
            } else {
                pCi = Abc_NtkCi(pNtk, j);
                std::string tmp  = Abc_ObjName(pCi);
                mark[tmp] = 1;
                int status1 = Solving(pCnf, nCnf, pSat, resCis, i, j, 1);
                if (status1 != l_True) {
                    outputNate[0].push_back(tmp); 
                }
                int status2 = Solving(pCnf, nCnf, pSat, resCis, i, j, 0);
                if (status2 != l_True) {
                    outputNate[1].push_back(tmp); 
                }
                if (status1 == l_True && status2 == l_True) {
                    outputNate[2].push_back(tmp); 
                }
                j++;
            }
        }
        int order[] = {0, 1, 2};
        if (reverse) {
            order[0] = 1;
            order[1] = 0;
        }
        printf("node %s:\n", Abc_ObjName(pObj));
        for (int j = 0; j < 3; j++) {
            int index = order[j];
            if (outputNate[index].size() > 0) {
                printf("%s inputs: ", nate[j]);
                int size = outputNate[index].size();
                for (int k = 0; k < size-1; k++) {
                    printf("%s,", outputNate[index][k].c_str());
                }
                printf("%s\n", outputNate[index][size-1].c_str());
            }
        }
    }
    Cnf_DataFree(pCnf);
    Cnf_DataFree(nCnf);
    sat_solver_delete( pSat );
}

int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
            default:
                Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
                return 1;
        }
    }
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk)) { // Aig network
        Abc_Print(-1, "Showing PO unate information can only be done for logic AIG networks.\n");
        return 1;
    }
    int fUseAllCis = 0, i; 
    Abc_Obj_t* pObj;
    Abc_Ntk_t* pNtkRes;
    Abc_NtkForEachPo( pNtk, pObj, i ) {                                      
        Abc_Obj_t* p;
        p = Abc_NtkFindNode(pNtk, Abc_ObjName(pObj));

        pNtkRes = Abc_NtkCreateCone( pNtk, p, Abc_ObjName(pObj), fUseAllCis);
        int reverse = 0;
        if ((Abc_NtkPo(pNtkRes, 0)->fCompl0 + Abc_NtkPo(pNtk, i)->fCompl0 )== 1) {
            reverse = 1;
        }
        Abc_PrintPounate(pNtkRes, pNtk, reverse);
    }
    return 0;
/*
usage:
    Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
    Abc_Print(-2, "\t       print unate information for Primary output in the AIG network\n");
    Abc_Print(-2, "\t-h   : print the command usage\n");
    return 1;
    */
}
