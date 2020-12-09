#include <vector>
#include <algorithm>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "lsvCmdPrintPOUnate.h"
#include "lsvUtils.h"

using namespace std;

extern "C" Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);

const int LSV_UNATENESS_NUM = 3;
const int LSV_POSITIVE_UNATE_CHECK_FAIL = 1,
          LSV_NEGATIVE_UNATE_CHECK_FAIL = 2;
const int LSV_POSITIVE_UNATE_FLAG = LSV_NEGATIVE_UNATE_CHECK_FAIL,
          LSV_NEGATIVE_UNATE_FLAG = LSV_POSITIVE_UNATE_CHECK_FAIL,
          LSV_BINATE_FLAG = LSV_POSITIVE_UNATE_CHECK_FAIL | LSV_NEGATIVE_UNATE_CHECK_FAIL,
          LSV_NOUNATENESS_FLAG = 0;

const int LSV_NOUNATENESS = -1,
          LSV_POSITIVE_UNATE = 0,
          LSV_NEGATIVE_UNATE = 1,
          LSV_BINATE = 2;

static const char *UNATE_NAME[LSV_UNATENESS_NUM] = { "+unate", "-unate", "binate" };

static void __Lsv_NtkPrintPOUnate_Cone(Abc_Ntk_t* pConeNtk, Abc_Ntk_t* pParentNtk, int fCompl);

void Lsv_NtkPrintPOUnate(Abc_Ntk_t* pNtk) {
    int i = 0;
    Abc_Obj_t *pPO;
    Abc_NtkForEachPo(pNtk, pPO, i) {
        Abc_Ntk_t* pConeNtk = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPO), Abc_ObjName(pPO), 0);
        __Lsv_NtkPrintPOUnate_Cone(pConeNtk, pNtk, Abc_ObjFaninC0(pPO));
        Abc_NtkDelete(pConeNtk);
    }
}

static void __Lsv_NtkPrintPOUnate_Cone(Abc_Ntk_t* pConeNtk, Abc_Ntk_t* pParentNtk, int fCompl) {
    Aig_Man_t *pMan = Abc_NtkToDar(pConeNtk, 0, 0);
    Cnf_Dat_t *pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    int i = 0;
    int j = 0;
    int nVars = pCnf->nVars;
    int nPI = Abc_NtkPiNum(pConeNtk);

    Cnf_Dat_t *pCnf_negcf = Cnf_DataDup(pCnf);
    Cnf_DataLift(pCnf_negcf, nVars);

    sat_solver *pSat = (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0);
    pSat = (sat_solver *)Cnf_DataWriteIntoSolverInt(pSat, pCnf_negcf, 1, 0);

    Aig_Obj_t *pPO;
    Abc_Obj_t *pPI_parent, *pPI_cone;
    sat_solver_setnvars(pSat, pSat->size + nPI);
    Abc_NtkForEachPi(pConeNtk, pPI_cone, i) {
        int pi_var = pCnf->pVarNums[pPI_cone->Id];
        sat_solver_add_buffer_enable(pSat, pi_var, pi_var + nVars, i + nVars*2, 0);
    }

    int constraint_len = nPI + 2 + 2;
    lit *constraint = ABC_ALLOC(lit, constraint_len);
    for(i = 0; i < constraint_len; i++) {
        constraint[i] = toLitCond(i + nVars*2, 0);
    }

    vector<Abc_Obj_t> unateness_vecs[LSV_UNATENESS_NUM];
    char unateness = 0;
    int pi_index = 0;
    Aig_ManForEachCo(pMan, pPO, i) {
        int po_var = pCnf->pVarNums[pPO->Id];
        Abc_NtkForEachPi(pParentNtk, pPI_parent, j) {
            unateness = 0;
            pPI_cone = Abc_NtkFindCi(pConeNtk, Abc_ObjName(pPI_parent));
            if (pPI_cone) {
                int pi_var = pCnf->pVarNums[pPI_cone->Id];
                // Set current PI constraint with X_1 = 1, X_2 = 0 to do
                // positive and negative cofactor, respectively
                constraint[pi_index] = toLitCond(pi_index + nVars*2, 1);
                constraint[nPI] = toLitCond(pi_var, 0);
                constraint[nPI+1] = toLitCond(pi_var + nVars, 1);

                // Positive Unate Check
                constraint[nPI+2] = toLitCond(po_var, 1);
                constraint[nPI+3] = toLitCond(po_var + nVars, 0);
                int ret = sat_solver_solve(pSat, constraint, (constraint + constraint_len), 0, 0, 0, 0);
                unateness |= (ret == l_True)
                    ? (!fCompl ? LSV_POSITIVE_UNATE_CHECK_FAIL : LSV_NEGATIVE_UNATE_CHECK_FAIL)
                    : 0;

                // Negative Unate Check
                constraint[nPI+2] = toLitCond(po_var, 0);
                constraint[nPI+3] = toLitCond(po_var + nVars, 1);
                ret = sat_solver_solve(pSat, constraint, (constraint + constraint_len), 0, 0, 0, 0);
                unateness |= (ret == l_True)
                    ? (!fCompl ? LSV_NEGATIVE_UNATE_CHECK_FAIL : LSV_POSITIVE_UNATE_CHECK_FAIL)
                    : 0;
                
                // Reset the current PI constraint to X_1 = X_2
                constraint[pi_index] = toLitCond(pi_index + nVars*2, 0);
                pi_index++;
            }

            switch (unateness)
            {
                case LSV_POSITIVE_UNATE_FLAG: {
                    unateness_vecs[LSV_POSITIVE_UNATE].push_back(*pPI_parent);
                    break;
                }
                case LSV_NEGATIVE_UNATE_FLAG: {
                    unateness_vecs[LSV_NEGATIVE_UNATE].push_back(*pPI_parent);
                    break;
                }
                case LSV_BINATE_FLAG: {
                    unateness_vecs[LSV_BINATE].push_back(*pPI_parent);
                    break;
                }
                default: {
                    unateness_vecs[LSV_POSITIVE_UNATE].push_back(*pPI_parent);
                    unateness_vecs[LSV_NEGATIVE_UNATE].push_back(*pPI_parent);
                    break;
                }
            }
        }

        printf("node %s:\n", Abc_ObjName(Abc_NtkPo(pConeNtk, i)));
        for(int p = 0; p < LSV_UNATENESS_NUM; p++) {
            if (!unateness_vecs[p].empty()) {
                sort(unateness_vecs[p].begin(), unateness_vecs[p].end(), Lsv_CmpAbcObjId);
                printf("%s inputs: ", UNATE_NAME[p]);
                Lsv_UtilPrintAbcObjVecs(unateness_vecs[p]);
                puts("");
            }
            unateness_vecs[p].clear();
        }
    }

    // Clean up
    ABC_FREE(constraint);
    sat_solver_delete(pSat);
    Cnf_DataFree(pCnf);
    Cnf_DataFree(pCnf_negcf);
    Cnf_ManFree();
    Aig_ManStop(pMan);
}

int Lsv_CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
    Lsv_NtkPrintPOUnate(pNtk);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
    Abc_Print(-2, "\t        print the unateness for each PO in terms of all PIs\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
