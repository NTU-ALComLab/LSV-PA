#include <vector>
#include <string>
#include <algorithm>
#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"

#include "lsvNtkUnate.h"

// ABC_NAMESPACE_IMPL_START
using namespace std;

int Lsv_NtkPrintSopUnate(Abc_Ntk_t *pNtk)
{
    int i, j;
    int nFanins;
    Abc_Obj_t *pObj;
    char *pSop, *pCube;
    int type, id;
    char val;
    int numBinate;
    Vec_Int_t *vType;
    Vec_Int_t *punate, *nunate, *binate;

    Abc_NtkForEachNode(pNtk, pObj, i)
    {
        nFanins = Abc_ObjFaninNum(pObj);
        if (nFanins == 0)
            continue;

        vType = Vec_IntStart(nFanins);

        pSop = (char *)pObj->pData;
        // check unateness
        Abc_SopForEachCube(pSop, nFanins, pCube)
        {
            numBinate = 0;
            Abc_CubeForEachVar(pCube, val, j)
            {
                type = Vec_IntGetEntry(vType, j);
                if (type == UNKNOWN)
                {
                    if (val == '0')
                        Vec_IntWriteEntry(vType, j, NEGUNATE);
                    else if (val == '1')
                        Vec_IntWriteEntry(vType, j, POSUNATE);
                }
                else if (type == POSUNATE)
                {
                    if (val == '0')
                        Vec_IntWriteEntry(vType, j, BINATE);
                }
                else if (type == NEGUNATE)
                {
                    if (val == '1')
                        Vec_IntWriteEntry(vType, j, BINATE);
                }
                else if (type == BINATE)
                {
                    numBinate++;
                }
                else
                {
                    printf("!!!Impossible state!!!\n");
                }
            }
            // early stop if all binate
            if (numBinate == nFanins)
                break;
        }

        // flip if the sop is offset
        if (Abc_SopIsComplement(pSop))
        {
            Vec_IntForEachEntry(vType, type, j)
            {
                if (type == POSUNATE)
                    Vec_IntWriteEntry(vType, j, NEGUNATE);
                else if (type == NEGUNATE)
                    Vec_IntWriteEntry(vType, j, POSUNATE);
            }
        }

        punate = Vec_IntAlloc(nFanins);
        nunate = Vec_IntAlloc(nFanins);
        binate = Vec_IntAlloc(nFanins);

        // summarize types of fanins
        Vec_IntForEachEntry(vType, type, j)
        {
            id = Abc_ObjId(Abc_ObjFanin(pObj, j));
            if (type == POSUNATE)
                Vec_IntPush(punate, id);
            else if (type == NEGUNATE)
                Vec_IntPush(nunate, id);
            else if (type == BINATE)
                Vec_IntPush(binate, id);
            else if (type == UNKNOWN)
            {
                Vec_IntPush(punate, id);
                Vec_IntPush(nunate, id);
            }
        }

        Vec_IntSort(punate, 0);
        Vec_IntSort(nunate, 0);
        Vec_IntSort(binate, 0);

        printNodeUnate(Abc_ObjName(pObj), pNtk, punate, nunate, binate);

        Vec_IntFree(vType);
        Vec_IntFree(punate);
        Vec_IntFree(nunate);
        Vec_IntFree(binate);
    }

    return 0;
}

int Lsv_NtkPrintPoUnate(Abc_Ntk_t *pNtk)
{
    Aig_Man_t *pMan;
    sat_solver *pSat;
    Cnf_Dat_t *pCnfPos, *pCnfNeg;
    Aig_Obj_t *pObj, *pPo, *pPi;
    int i, j;
    Vec_Int_t *punate, *nunate, *binate;

    pMan = Abc_NtkToDar(pNtk, 0, 0);

    // derive cnf formula of ntk
    pCnfPos = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    pCnfNeg = Cnf_DataDup(pCnfPos);
    Cnf_DataLift(pCnfNeg, pCnfPos->nVars);

    pSat = sat_solver_new();

    sat_solver_setnvars(pSat, pCnfPos->nVars + pCnfNeg->nVars);
    addCnfClauses(pSat, pCnfPos);
    addCnfClauses(pSat, pCnfNeg);

    int numPi = Aig_ManCiNum(pMan);
    int *alphas = new int[numPi];

    // create alphas for incremental sat
    Aig_ManForEachCi(pMan, pObj, i)
    {
        int id = Aig_ObjId(pObj);
        int posId = pCnfPos->pVarNums[id];
        int negId = pCnfNeg->pVarNums[id];
        alphas[i] = sat_solver_addvar(pSat);
        sat_solver_add_buffer_enable(pSat, posId, negId, alphas[i], 0);
    }

    // prove unateness
    Aig_ManForEachCo(pMan, pPo, i)
    {
        punate = Vec_IntAlloc(numPi);
        nunate = Vec_IntAlloc(numPi);
        binate = Vec_IntAlloc(numPi);
        // printf("%s\n", Abc_ObjName(Abc_NtkPo(pNtk, i)));
        Aig_ManForEachCi(pMan, pPi, j)
        {
            // printf("%s\n", Abc_ObjName(Abc_NtkPi(pNtk, j)));
            int binate_flag = 1;

            // positive unate
            if (proofUnate(pMan, pSat, pCnfPos, pCnfNeg, i, j, alphas, 1))
            {
                Vec_IntPush(punate, Abc_ObjId(Abc_NtkPi(pNtk, j)));
                binate_flag = 0;
            }
            // negative unate
            if (proofUnate(pMan, pSat, pCnfPos, pCnfNeg, i, j, alphas, 0))
            {
                Vec_IntPush(nunate, Abc_ObjId(Abc_NtkPi(pNtk, j)));
                binate_flag = 0;
            }
            // binate
            if (binate_flag)
            {
                Vec_IntPush(binate, Abc_ObjId(Abc_NtkPi(pNtk, j)));
            }
        }

        printNodeUnate(Abc_ObjName(Abc_NtkPo(pNtk, i)), pNtk, punate, nunate, binate);

        Vec_IntFree(punate);
        Vec_IntFree(nunate);
        Vec_IntFree(binate);
    }

    Cnf_DataFree(pCnfPos);
    Cnf_DataFree(pCnfNeg);
    delete alphas;
    sat_solver_delete(pSat);
    Aig_ManStop(pMan);

    return 0;
}

void printNodeUnate(char *name, Abc_Ntk_t *pNtk, Vec_Int_t *punate, Vec_Int_t *nunate, Vec_Int_t *binate)
{
    int id, j;

    printf("node %s:\n", name);

    // print results
    if (Vec_IntSize(punate) != 0)
    {
        printf("+unate inputs:");
        Vec_IntForEachEntry(punate, id, j)
        {
            name = Abc_ObjName(Abc_NtkObj(pNtk, id));
            if (j == 0)
                printf(" %s", name);
            else
                printf(",%s", name);
        }
        printf("\n");
    }
    if (Vec_IntSize(nunate) != 0)
    {
        printf("-unate inputs:");
        Vec_IntForEachEntry(nunate, id, j)
        {
            name = Abc_ObjName(Abc_NtkObj(pNtk, id));
            if (j == 0)
                printf(" %s", name);
            else
                printf(",%s", name);
        }
        printf("\n");
    }
    if (Vec_IntSize(binate) != 0)
    {
        printf("binate inputs:");
        Vec_IntForEachEntry(binate, id, j)
        {
            name = Abc_ObjName(Abc_NtkObj(pNtk, id));
            if (j == 0)
                printf(" %s", name);
            else
                printf(",%s", name);
        }
        printf("\n");
    }
}

void addCnfClauses(sat_solver *pSat, Cnf_Dat_t *pCnf)
{
    int i;
    for (i = 0; i < pCnf->nClauses; i++)
    {
        sat_solver_addclause(pSat, pCnf->pClauses[i], pCnf->pClauses[i + 1]);
    }
}

int proofUnate(Aig_Man_t *pMan, sat_solver *pSat, Cnf_Dat_t *pCnfPos, Cnf_Dat_t *pCnfNeg, int po, int pi, int *alphas, int flag)
{
    int i;
    Aig_Obj_t *pObj;
    int piNum = Aig_ManCiNum(pMan);
    int *lits = new int[piNum + 4];
    int RetValue = 0;
    int status;

    // create assumptions
    Aig_ManForEachCi(pMan, pObj, i)
    {
        lits[i] = toLitCond(alphas[i], (i == pi));
    }

    // if flag == 1, pos unate
    // if flag == 0, neg unate
    lits[piNum] = toLitCond(pCnfPos->pVarNums[Aig_ObjId(Aig_ManCi(pMan, pi))], 0);
    lits[piNum + 1] = toLitCond(pCnfNeg->pVarNums[Aig_ObjId(Aig_ManCi(pMan, pi))], 1);
    lits[piNum + 2] = toLitCond(pCnfPos->pVarNums[Aig_ObjId(Aig_ManCo(pMan, po))], flag);
    lits[piNum + 3] = toLitCond(pCnfNeg->pVarNums[Aig_ObjId(Aig_ManCo(pMan, po))], !flag);

    sat_solver_simplify(pSat);
    status = sat_solver_solve(pSat, lits, lits + (piNum + 4), 0, 0, 0, 0);

    if (status == l_Undef)
    {
        //        printf( "The problem timed out.\n" );
        RetValue = -1;
    }
    else if (status == l_True)
    {
        //        printf( "The problem is SATISFIABLE.\n" );
        RetValue = 0;
    }
    else if (status == l_False)
    {
        //        printf( "The problem is UNSATISFIABLE.\n" );
        RetValue = 1;
    }

    /*
    if (status == l_True)
    {
        printf("In pi = %d, po = %d, flag = %d\n", pi, po, flag);
        Aig_ManForEachCi(pMan, pObj, i)
        {
            int val = sat_solver_var_value(pSat, pCnfPos->pVarNums[Aig_ObjId(Aig_ManCi(pMan, i))]);
            printf("Pi%d = %d, ", i, val);
        }
        Aig_ManForEachCo(pMan, pObj, i)
        {
            int val = sat_solver_var_value(pSat, pCnfPos->pVarNums[Aig_ObjId(Aig_ManCo(pMan, i))]);
            printf("Po%d = %d, ", i, val);
        }
        printf("\n");
        Aig_ManForEachCi(pMan, pObj, i)
        {
            int val = sat_solver_var_value(pSat, pCnfNeg->pVarNums[Aig_ObjId(Aig_ManCi(pMan, i))]);
            printf("Pi%d = %d, ", i, val);
        }
        Aig_ManForEachCo(pMan, pObj, i)
        {
            int val = sat_solver_var_value(pSat, pCnfNeg->pVarNums[Aig_ObjId(Aig_ManCo(pMan, i))]);
            printf("Po%d = %d, ", i, val);
        }
        printf("\n");
    }
    */

    delete lits;

    return RetValue;
}

// ABC_NAMESPACE_IMPL_END
