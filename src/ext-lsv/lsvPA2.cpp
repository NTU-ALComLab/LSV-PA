#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include <cstdlib>
//#define LSVDBG

extern "C" Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t*, int, int);
extern "C" Abc_Ntk_t* Abc_NtkCreateCone(Abc_Ntk_t*, Abc_Obj_t*, char*, int);

static int Lsv_CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPOUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

int cmp(const void *a, const void *b) {
    Abc_Obj_t* obj_a = *(Abc_Obj_t**)a;
    Abc_Obj_t* obj_b = *(Abc_Obj_t**)b;

    if (Abc_ObjId(obj_a) < Abc_ObjId(obj_b))
        return -1;
    else if (Abc_ObjId(obj_a) == Abc_ObjId(obj_b)) 
        return 0;
    else 
        return 1;
}

void Lsv_NtkPrintPOUnate(Abc_Ntk_t* pNtk) {
    Aig_Obj_t *pAigObj;
    Abc_Obj_t *pPO, *pPOs, *pPI, *pPIs;
    int po_id = 0;
    int i, j, k;
    int num_pi = Abc_NtkPiNum(pNtk);
    int p_status[num_pi + 10];
    int n_status[num_pi + 10];
    int num_punate, num_nunate, num_binate;
    Abc_Obj_t *punate[num_pi], *nunate[num_pi], *binate[num_pi];
    int num_assum = num_pi + 4;
    lit assum[num_assum];
    int assum_base;
    Abc_Ntk_t* pNtks;
    Aig_Man_t* pMan;
    Cnf_Dat_t* lCnf;
    Cnf_Dat_t* rCnf;
    sat_solver* pSat;

    // Assert AIG
    assert(Abc_NtkIsStrash(pNtk));
    assert(Abc_NtkLatchNum(pNtk) == 0);

    // For Each PO
    Abc_NtkForEachPo(pNtk, pPO, i) {
        // Cone and Convert to AIG
        pNtks     = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPO), Abc_ObjName(pPO), 0);
        num_assum = Abc_NtkPiNum(pNtks) + 4;
        pMan      = Abc_NtkToDar(pNtks, 0, 0);
        Aig_ManForEachPoSeq(pMan, pAigObj, j) {
            po_id = Aig_ObjId(pAigObj);
        }

        // Convert to CNF
        lCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
        rCnf = Cnf_DataDup(lCnf);
        Cnf_DataLift(rCnf, rCnf->nVars);
        assum_base = lCnf->nVars * 2;
#ifdef LSVDBG
        Cnf_DataPrint(lCnf, 1);
        Cnf_DataPrint(rCnf, 1);
#endif

        // Creat solver
        pSat = (sat_solver *)Cnf_DataWriteIntoSolver(lCnf, 1, 0);
        Cnf_DataWriteIntoSolverInt(pSat, rCnf, 1, 0);

        Abc_NtkForEachPi(pNtks, pPIs, j) {
            sat_solver_add_buffer_enable(pSat,  \
                    lCnf->pVarNums[Abc_ObjId(pPIs)], \
                    rCnf->pVarNums[Abc_ObjId(pPIs)], \
                    assum_base + j, 0);
            assum[4 + j] = Abc_Var2Lit(assum_base + j, 0); // Positive
        }
#ifdef LSVDBG
        printf("        nVars\tnClauses\n");
        printf("lCNF:   %d\t%d\n", lCnf->nVars, lCnf->nClauses);
        printf("rCNF:   %d\t%d\n", rCnf->nVars, rCnf->nClauses);
        printf("SOLVER: %d\t%d\n", sat_solver_nvars(pSat), sat_solver_nclauses(pSat));
        printf("\n");
#endif

        // Assert PO Value
        // Correction the Output of Cone
        Abc_NtkForEachPo(pNtks, pPOs, j) {
            if (Abc_ObjFaninC0(pPO) == Abc_ObjFaninC0(pPOs)) {
                assum[0] = Abc_Var2Lit(lCnf->pVarNums[po_id], 0); // Positive
                assum[1] = Abc_Var2Lit(rCnf->pVarNums[po_id], 1); // Negative
            }
            else {
                assum[0] = Abc_Var2Lit(lCnf->pVarNums[po_id], 1); // Positive
                assum[1] = Abc_Var2Lit(rCnf->pVarNums[po_id], 0); // Negative
            }
        }

        // Solve Each PIs
        Abc_NtkForEachPi(pNtks, pPIs, j) {
            assum[4 + j] = Abc_Var2Lit(assum_base + j, 1); // Negative

            // TEST positive unate
            assum[2]    = Abc_Var2Lit(lCnf->pVarNums[Abc_ObjId(pPIs)], 1);
            assum[3]    = Abc_Var2Lit(rCnf->pVarNums[Abc_ObjId(pPIs)], 0);
            p_status[j] = sat_solver_solve(pSat, assum, assum + num_assum, \
                    (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);

            // TEST negative unate
            assum[2]    = Abc_Var2Lit(lCnf->pVarNums[Abc_ObjId(pPIs)], 0);
            assum[3]    = Abc_Var2Lit(rCnf->pVarNums[Abc_ObjId(pPIs)], 1);
            n_status[j] = sat_solver_solve(pSat, assum, assum + num_assum, \
                    (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);

            assum[4 + j] = Abc_Var2Lit(assum_base + j, 0); // Positive
        }

        // Solve Each PI
        num_punate = num_nunate = num_binate = 0;
        Abc_NtkForEachPi(pNtk, pPI, j) {
            int fl = 1;
            Abc_NtkForEachPi(pNtks, pPIs, k) {
                if (strcmp(Abc_ObjName(pPI), Abc_ObjName(pPIs)) == 0) {
                    fl = 0;
                    break;
                }
            }
            if (fl) {
                punate[num_punate++] = pPI;
                nunate[num_nunate++] = pPI;
            }
            else {
                if (p_status[k] == l_False)
                    punate[num_punate++] = pPI;
                if (n_status[k] == l_False)
                    nunate[num_nunate++] = pPI;
                if (p_status[k] != l_False && n_status[k] != l_False)
                    binate[num_binate++] = pPI;
            }
        }
        qsort((void*)punate, num_punate, sizeof(Abc_Obj_t*), cmp);
        qsort((void*)nunate, num_nunate, sizeof(Abc_Obj_t*), cmp);
        qsort((void*)binate, num_binate, sizeof(Abc_Obj_t*), cmp);

        // Output Results
        printf("node %s:\n", Abc_ObjName(pPO));
        if (num_punate) {
            printf("+unate inputs: %s", Abc_ObjName(punate[0]));
            for (j = 1; j < num_punate; ++j)
                printf(",%s", Abc_ObjName(punate[j]));
            printf("\n");
        }
        if (num_nunate) {
            printf("-unate inputs: %s", Abc_ObjName(nunate[0]));
            for (j = 1; j < num_nunate; ++j)
                printf(",%s", Abc_ObjName(nunate[j]));
            printf("\n");
        }
        if (num_binate) {
            printf("binate inputs: %s", Abc_ObjName(binate[0]));
            for (j = 1; j < num_binate; ++j)
                printf(",%s", Abc_ObjName(binate[j]));
            printf("\n");
        }
        sat_solver_delete(pSat);
    }
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
    Abc_Print(-2, "\t        print the unate information for each primary output in terms of all primary inputs, whose function is encoded as an and-inverter graph (AIG).\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
