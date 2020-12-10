#include "aig/aig/aig.h"
#include "base/abc/abc.h"
#include "ext-lsv/lsv.h"
#include "sat/bsat/satSolver.h"
#include "sat/bsat/satVec.h"
#include "sat/cnf/cnf.h"
#include <climits>
#include <iostream>
#include <set>
#include <vector>

static bool proveUnate(Aig_Man_t *pMan, sat_solver *p, Cnf_Dat_t *pPos,
                       Cnf_Dat_t *pNeg, std::vector<int> &alphas, int index,
                       bool isPositive);
static void provePOIncremental(Abc_Ntk_t *pNtk);
static void printLSVUnate(Abc_Ntk_t *pNtk);

static std::vector<int> positive_unate;
static std::vector<int> negative_unate;
static std::vector<int> binate;
static std::vector<int> non_support;
static std::vector<int> ci_mappings;

void Lsv_NtkPrintUnatePo(Abc_Ntk_t *pNtk) {
    Abc_Obj_t *pPo;
    int i;
    Abc_NtkForEachPo(pNtk, pPo, i) {
        // create cone for each PO
        std::cout << "node " << Abc_ObjName(pPo) << ":" << std::endl;
        positive_unate.clear();
        negative_unate.clear();
        binate.clear();
        ci_mappings.clear();
        non_support.clear();
        Abc_Ntk_t *pPoCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 0);

        if (Abc_ObjFaninC0(pPo)) {
            Abc_ObjSetFaninC( Abc_NtkPo(pPoCone, 0) , 0 );
        }
        // save non-support variables
        int j = 0;
        ci_mappings.reserve(Abc_NtkCiNum(pPoCone));
        for (int i = 0; i < Abc_NtkCiNum(pNtk); ++i) {
            if (j < (Abc_NtkCiNum(pPoCone)) && strcmp(Abc_ObjName(Abc_NtkCi(pNtk, i)), Abc_ObjName(Abc_NtkCi(pPoCone, j))) == 0) {
                ci_mappings[j] = i;
                ++j;
                continue;
            }
            non_support.push_back(i);
        }
        assert(j == Abc_NtkCiNum(pPoCone));
        provePOIncremental(pPoCone);
        printLSVUnate(pNtk);
    }
}

void provePOIncremental(Abc_Ntk_t *pNtk) {
    Aig_Man_t *pMan;
    Aig_Obj_t *pObj;
    int *pBeg, *pEnd;
    int i;
    sat_solver *solver = sat_solver_new();
    pMan = Abc_NtkToDar(pNtk, 0, 0);

    // create two cnf for positive unate and negative unate
    Cnf_Dat_t *pCnfPositive = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    Cnf_Dat_t *pCnfNegative = Cnf_DataDup(pCnfPositive);
    Cnf_DataLift(pCnfNegative, pCnfPositive->nVars);
    sat_solver_setnvars(solver, Aig_ManObjNum(pMan) * 2);

    Cnf_CnfForClause(pCnfPositive, pBeg, pEnd, i) {
        sat_solver_addclause(solver, pBeg, pEnd);
    }
    Cnf_CnfForClause(pCnfNegative, pBeg, pEnd, i) {
        sat_solver_addclause(solver, pBeg, pEnd);
    }

    // create alpha variables
    std::vector<int> alphas;
    Aig_ManForEachCi(pMan, pObj, i) {
        int var = sat_solver_addvar(solver);
        sat_solver_add_buffer_enable(
            solver, pCnfPositive->pVarNums[Aig_ObjId(pObj)],
            pCnfNegative->pVarNums[Aig_ObjId(pObj)], var, 0);
        alphas.push_back(var);
    }

    // actually proving
    Aig_ManForEachCi(pMan, pObj, i) {
        // TODO
        bool isUnatePos = false, isUnateNeg = false;
        if (proveUnate(pMan, solver, pCnfPositive, pCnfNegative, alphas, i, true)) {
            isUnatePos = true;
            positive_unate.push_back(i);
        }
        if (proveUnate(pMan, solver, pCnfPositive, pCnfNegative, alphas, i,
                       false)) {
            isUnateNeg = true;
            negative_unate.push_back(i);
        }
        if (!isUnatePos && !isUnateNeg)
            binate.push_back(i);
    }

    // deconstruct managers
    Cnf_DataFree(pCnfPositive);
    Cnf_DataFree(pCnfNegative);
    Aig_ManStop(pMan);
    sat_solver_delete(solver);
}

bool proveUnate(Aig_Man_t *pMan, sat_solver *p, Cnf_Dat_t *pPos,
                Cnf_Dat_t *pNeg, std::vector<int> &alphas, int index,
                bool isPositive) {
    // create lits for assumption
    int lits[Aig_ManCiNum(pMan) + 4];
    for (int i = 0; i < alphas.size(); ++i) {
        if (i == index)
            lits[i] = toLitCond(alphas[i], 1);
        else
            lits[i] = toLitCond(alphas[i], 0);
    }
    lits[Aig_ManCiNum(pMan)] =
        toLitCond(pPos->pVarNums[Aig_ObjId(Aig_ManCi(pMan, index))], 0);
    lits[Aig_ManCiNum(pMan) + 1] =
        toLitCond(pNeg->pVarNums[Aig_ObjId(Aig_ManCi(pMan, index))], 1);
    if (isPositive) {
        lits[Aig_ManCiNum(pMan) + 2] =
            toLitCond(pPos->pVarNums[Aig_ObjId(Aig_ManCo(pMan, 0))], 1);
        lits[Aig_ManCiNum(pMan) + 3] =
            toLitCond(pNeg->pVarNums[Aig_ObjId(Aig_ManCo(pMan, 0))], 0);
    } else {
        lits[Aig_ManCiNum(pMan) + 2] =
            toLitCond(pPos->pVarNums[Aig_ObjId(Aig_ManCo(pMan, 0))], 0);
        lits[Aig_ManCiNum(pMan) + 3] =
            toLitCond(pNeg->pVarNums[Aig_ObjId(Aig_ManCo(pMan, 0))], 1);
    }
    // UNSAT
    if (sat_solver_solve(p, lits, lits + Aig_ManCiNum(pMan) + 4, 0, 0, 0, 0) ==
        l_False) {
        /* std::cout << "UNSAT" << std::endl; */
        return true;
    }
    return false;
}

void printLSVUnate(Abc_Ntk_t *pNtk) {
    if (positive_unate.size() != 0 || non_support.size() != 0) {
        std::cout << "+unate inputs: ";
        bool first = true;
        int i = 0, j = 0;
        while (i < positive_unate.size() || j < non_support.size()) {
            if (!first)
                std::cout << ",";
            if (j == non_support.size() || (i != positive_unate.size() && ci_mappings[positive_unate[i]] < non_support[j])) {
                std::cout << Abc_ObjName(
                    Abc_NtkPi(pNtk, ci_mappings[positive_unate[i]]));
                ++i;
            } else {
                std::cout << Abc_ObjName(Abc_NtkPi(pNtk, non_support[j]));
                ++j;
            }
            if (first)
                first = false;
        }
        std::cout << std::endl;
    }
    if (negative_unate.size() != 0 || non_support.size() != 0) {
        std::cout << "-unate inputs: ";
        bool first = true;
        int i = 0, j = 0;
        while (i < negative_unate.size() || j < non_support.size()) {
            if (!first)
                std::cout << ",";
            if (j == non_support.size() || (i != negative_unate.size() && ci_mappings[negative_unate[i]] < non_support[j])) {
                std::cout << Abc_ObjName(Abc_NtkPi(pNtk, ci_mappings[negative_unate[i]]));
                ++i;
            } else {
                std::cout << Abc_ObjName(Abc_NtkPi(pNtk, non_support[j]));
                ++j;
            }
            if (first)
                first = false;
        }
        std::cout << std::endl;
    }
    if (binate.size() != 0) {
        std::cout << "binate inputs: ";
        for (int o : binate) {
            if (o != *binate.begin())
                std::cout << ",";
            std::cout << Abc_ObjName(Abc_NtkPi(pNtk, ci_mappings[o]));
        }
        std::cout << std::endl;
    }
}
