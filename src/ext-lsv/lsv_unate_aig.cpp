#include <iostream>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "sat/cnf/cnf.h"

#include "sat/bsat/satSolver.h"

#include "misc/vec/vec.h"

#include <deque>
#include <map>
#include <algorithm>
#include <vector>
#include <string>
#include <unordered_map>
#include "aig/aig/aig.h"
using namespace std;


extern "C"{
    Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

static int VarToLit(int v, int s){
    return (v << 1) ^ (s & 1);
}

int out_lit(Cnf_Dat_t* pCnf, Aig_Obj_t* pCo, bool want1)
{
    Aig_Obj_t* f = Aig_ObjFanin0(pCo);
    int var = pCnf->pVarNums[Aig_ObjId(f)];

    // actual desired value after edge inversion
    bool desired = want1 ^ Aig_ObjFaninC0(pCo);

    // SAT literal: sign = 0 => var=1, sign = 1 => var=0
    int sign = desired ? 0 : 1;

    return VarToLit(var, sign);
}

static std::string BuildWitnessByName(
    Abc_Ntk_t* pNtkOrig, Abc_Ntk_t* pCone, Aig_Man_t* pAigCone,
    Cnf_Dat_t* pCnfA, sat_solver* pSat, int xiOrigIdx
){
    int nOrigPis = Abc_NtkPiNum(pNtkOrig);
    std::string result(nOrigPis, '0');

    // Map PI name → original PI index
    std::unordered_map<std::string,int> nameToIdx;
    Abc_Obj_t* pPi;
    int idx = 0;
    Abc_NtkForEachPi(pNtkOrig, pPi, idx)
        nameToIdx[Abc_ObjName(pPi)] = idx;

    // Gather cone AIG CI nodes in order
    std::vector<Aig_Obj_t*> coneCi;
    Aig_Obj_t* pCi;
    int ciIdx = 0;
    Aig_ManForEachCi(pAigCone, pCi, ciIdx)
        coneCi.push_back(pCi);

    // For each PI in the cone network
    Abc_Obj_t* pConePi;
    int conePiIdx = 0;
    Abc_NtkForEachPi(pCone, pConePi, conePiIdx)
    {
        std::string name = Abc_ObjName(pConePi);

        // Find this PI in the original PI list
        auto it = nameToIdx.find(name);
        if (it == nameToIdx.end()) continue;

        int i = it->second;
        if (i == xiOrigIdx) continue;

        // CNF variable for this AIG CI
        int var = pCnfA->pVarNums[Aig_ObjId(coneCi[conePiIdx])];

        int val = (var >= 0) ? sat_solver_var_value(pSat, var) : 0;
        result[i] = val ? '1' : '0';
    }

    // Mark xi as don't care
    if (0 <= xiOrigIdx && xiOrigIdx < nOrigPis)
        result[xiOrigIdx] = '-';

    return result;
}


static void sat_add_equiv_clause(sat_solver* pSat, int vA, int vB)
{
    // (~vA or vB)
    {
        lit lits[2] = { toLitCond(vA, 1), toLitCond(vB, 0) };
        sat_solver_addclause(pSat, lits, lits + 2);
    }
    // (~vB or vA)
    {
        lit lits[2] = { toLitCond(vA, 0), toLitCond(vB, 1) };
        sat_solver_addclause(pSat, lits, lits + 2);
    }
}


int Abc_CommandCheckUnateAig(Abc_Frame_t *pAbc, int argc, char **argv){
    if (argc != 3) {
        Abc_Print(-1, "Usage: lsv_unate_aig <po> <ci>\n");
        return 1;
    }

    int k = atoi(argv[1]);   // output index
    int i = atoi(argv[2]);   // input index

    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int nPis = Abc_NtkPiNum(pNtk), nPos = Abc_NtkPoNum(pNtk);
    Abc_Obj_t* pPo   = Abc_NtkPo(pNtk, k);
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);
    Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, pRoot, Abc_ObjName(pPo), 1);
    int index = -1, t;
    Abc_Obj_t* ConePi;
    char* name = Abc_ObjName(Abc_NtkPi(pNtk, k));
    Abc_NtkForEachPi(pCone, ConePi, t){
        if(strcmp(Abc_ObjName(ConePi), name)){
            index = t;
            break;
        }
    }
    if(index == -1){
        printf("independent\n");
        return 0;
    }

    Abc_Ntk_t* StrCone = Abc_NtkStrash(pCone, 0, 0, 0);
    Aig_Man_t* pAig = Abc_NtkToDar(StrCone, 0, 0);
    Cnf_Dat_t* pCnfA = Cnf_Derive(pAig, 1);
    Cnf_Dat_t* pCnfB = Cnf_Derive(pAig, 1);
    int nVarsA = pCnfA->nVars;
    Cnf_DataLift(pCnfB, nVarsA);

    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars(pSat, pCnfA->nVars + pCnfB->nVars);
    Cnf_DataWriteIntoSolverInt(pSat, pCnfA, 1, 0);
    Cnf_DataWriteIntoSolverInt(pSat, pCnfB, 1, 0);

    vector<Aig_Obj_t*> vCi, vCo;
    Aig_Obj_t* Ptr;
    Aig_ManForEachCi(pAig, Ptr, t){
        vCi.push_back(Ptr);
    }
    Aig_ManForEachCo(pAig, Ptr, t){
        vCo.push_back(Ptr);
    }

    for(index = 0; index < vCi.size(); index++){
        if(index == i){
            continue;
        }
        int vA = pCnfA->pVarNums[Aig_ObjId(vCi[t])];
        int vB = pCnfB->pVarNums[Aig_ObjId(vCi[t])];
        if(vA > 0 && vB > 0){
            sat_add_equiv_clause(pSat, vA, vB);
        }
    }

    vector<int> as;
    int vXiA = pCnfA->pVarNums[Aig_ObjId(vCi[i])];
    int vXiB = pCnfB->pVarNums[Aig_ObjId(vCi[i])];
    if(vXiA >= 0 && vXiB >= 0){
        as.push_back(VarToLit(vXiA,1));
        as.push_back(VarToLit(vXiB,0));
    }
    as.push_back(out_lit(pCnfA, vCo[0], 1));
    as.push_back(out_lit(pCnfB, vCo[0], 0));
    int statusPos = sat_solver_solve(pSat, &as[0], &as[0]+(int)as.size(), 0,0,0,0);
    string w1 = BuildWitnessByName(pNtk, StrCone, pAig, pCnfA, pSat, i);
    
    as.clear();
    if(vXiA >= 0 && vXiB >= 0){
        as.push_back(VarToLit(vXiA,1));
        as.push_back(VarToLit(vXiB,0));
    }
    as.push_back(out_lit(pCnfA, vCo[0], 0));
    as.push_back(out_lit(pCnfB, vCo[0], 1));
    int statusNeg = sat_solver_solve(pSat, &as[0], &as[0]+(int)as.size(), 0,0,0,0);
    string w2 = BuildWitnessByName(pNtk, StrCone, pAig, pCnfA, pSat, i);
    int isPosUnate = (statusPos == l_False);
    int isNegUnate = (statusNeg == l_False);

    if(!isPosUnate && !isNegUnate){
        printf("independent\n");
    }
    else if(isPosUnate && !isNegUnate){
        printf("positive unate\n");
    }
    else if(isNegUnate && !isPosUnate){
        printf("negative unate\n");
    }
    else{
        printf("binate\n");
        cout << w1 << "\n";
        cout << w2 << "\n";
    }
    return 0;
}

