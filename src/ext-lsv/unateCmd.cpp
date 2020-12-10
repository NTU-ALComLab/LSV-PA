
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include <string.h>
#include <iostream>

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

using namespace std;
namespace
{

void printUnate(Abc_Ntk_t* pNtk, Abc_Obj_t* po, Vec_Int_t * posUnatePi, Vec_Int_t * negUnatePi, Vec_Int_t * binatePi)
{
    int i;
    cout << "node " << Abc_ObjName(po) << ":\n"; 
    if (Vec_IntSize(posUnatePi))
    {
        cout << "+unate inputs: ";
        for (i = 0; i < Vec_IntSize(posUnatePi); i++)
            if (i == Vec_IntSize(posUnatePi) - 1)
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(posUnatePi, i)));
            else
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(posUnatePi, i))) << ",";
        cout << "\n";
    }
    if (Vec_IntSize(negUnatePi))
    {
        cout << "-unate inputs: ";
        for (i = 0; i < Vec_IntSize(negUnatePi); i++)
            if (i == Vec_IntSize(negUnatePi) - 1)
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(negUnatePi, i)));
            else
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(negUnatePi, i))) << ",";
        cout << "\n";
    }
    if (Vec_IntSize(binatePi))
    {
        cout << "binate inputs: ";
        for (i = 0; i < Vec_IntSize(binatePi); i++)
            if (i == Vec_IntSize(binatePi) - 1)
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(binatePi, i)));
            else
                cout << Abc_ObjName(Abc_NtkObj(pNtk, Vec_IntGetEntry(binatePi, i))) << ",";
        cout << "\n";
    }
}

bool Vec_BitAll1(Vec_Bit_t * p)
{   
    int i;
    for (i = 0; i < Vec_BitSize(p); i++)
    {
        if (Vec_BitGetEntry(p, i) == 0)
            return 0;
    }
    return 1;
}

bool Vec_BitAll0(Vec_Bit_t * p)
{
    int i;
    for (i = 0; i < Vec_BitSize(p); i++)
    {
        if (Vec_BitGetEntry(p, i) == 1)
            return 0;
    }
    return 1;
}

void NodeUnate(Abc_Ntk_t* pNtk, Abc_Obj_t* pObj)
{
    int i;
    int FaninNum = Abc_ObjFaninNum(pObj);
    Vec_Int_t * posUnate = Vec_IntAlloc(0);
    Vec_Int_t * negUnate = Vec_IntAlloc(0);
    Vec_Int_t * binate = Vec_IntAlloc(0);
    Vec_Ptr_t * literalAppear = Vec_PtrAlloc(FaninNum);
    for (i = 0; i < FaninNum; i++)
    {
        Vec_Bit_t * tmp = Vec_BitAlloc(0);
        Vec_PtrPush(literalAppear, (void *)tmp);
    }

    // parse SOP string
    char *pCube, Value;
    char *pSop;
    pSop = (char *)Abc_ObjData(pObj);
    Abc_SopForEachCube(pSop, FaninNum, pCube) {
        Abc_CubeForEachVar(pCube, Value, i){
            if (Value == '1')
                Vec_BitPush((Vec_Bit_t *)Vec_PtrGetEntry(literalAppear, i), 1);
            else if (Value == '0')
                Vec_BitPush((Vec_Bit_t *)Vec_PtrGetEntry(literalAppear, i), 0);
        }
    }

    for (i = 0; i < FaninNum; i++)
    {
        Vec_Bit_t * p = (Vec_Bit_t *)Vec_PtrGetEntry(literalAppear, i);
        bool all1 = Vec_BitAll1(p), all0 = Vec_BitAll0(p);
        if (all1)
            Vec_IntPush(posUnate, Abc_ObjFaninId(pObj, i));
        if (all0)
            Vec_IntPush(negUnate, Abc_ObjFaninId(pObj, i));
        if (!(all1 || all0))
            Vec_IntPush(binate, Abc_ObjFaninId(pObj, i));
    }

    // sort in an increasing order w.r.t. ObjId
    Vec_IntSort(posUnate, 0);
    Vec_IntSort(negUnate, 0);
    Vec_IntSort(binate, 0);

    if (pSop[(FaninNum + 2) - 1] == '1') // onset
        printUnate(pNtk, pObj, posUnate, negUnate, binate);
    else // offset
        printUnate(pNtk, pObj, negUnate, posUnate, binate);
        
    /* free */
    for (i = 0; i < FaninNum; i++)
        Vec_BitFree((Vec_Bit_t *)Vec_PtrGetEntry(literalAppear, i));
    Vec_PtrFree(literalAppear);
    Vec_IntFree(posUnate);
    Vec_IntFree(negUnate);
    Vec_IntFree(binate);
}

int sopunate_Command(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t* pObj;
    if (!Abc_NtkIsSopLogic(pNtk))
    {
        cout << "[error]The network should be a Boolean network whose function is expressed in SOP." << endl;
        return -1;
    }
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        if (Abc_ObjFaninNum(pObj) != 0)
            NodeUnate(pNtk, pObj);
    }

    return 0;
} // namespace

void addClause(sat_solver * pSat, Aig_Man_t * pAig, Cnf_Dat_t * pCnfPos, Cnf_Dat_t * pCnfNeg, Vec_Int_t * iVarEn)
{
    int i;
    Aig_Obj_t * pObj;
    // add positive & negative cofactor networks
    for (i = 0; i < pCnfPos->nClauses; i++){
        sat_solver_addclause(pSat, pCnfPos->pClauses[i], pCnfPos->pClauses[i+1]);
    }
    for (i = 0; i < pCnfNeg->nClauses; i++){
        sat_solver_addclause(pSat, pCnfNeg->pClauses[i], pCnfNeg->pClauses[i+1]);
    }

    // add clauses asserting equivalence
    Aig_ManForEachCi(pAig, pObj, i){
        int iVar0 = pCnfPos->pVarNums[Aig_ObjId(pObj)];
        int iVar1 = pCnfNeg->pVarNums[Aig_ObjId(pObj)];
        Vec_IntPush(iVarEn, sat_solver_addvar(pSat));
        sat_solver_add_buffer_enable(pSat, iVar0, iVar1, Vec_IntGetEntry(iVarEn, Vec_IntSize(iVarEn)-1), 0);
    }
}

void poUnateSolve(sat_solver * pSat, Aig_Man_t * pAig, Cnf_Dat_t * pCnfPos, Cnf_Dat_t * pCnfNeg, Vec_Int_t * iVarEn, Vec_Int_t * unateAigCi)
{
    int i, j, status, isPosUnate, isNegUnate;
    Aig_Obj_t * pObj;
    int *Lits = new int[Aig_ManCiNum(pAig)+4];
    Aig_ManForEachCi(pAig, pObj, i){
        isPosUnate = 0;
        isNegUnate = 0;
        for (j = 0; j < Aig_ManCiNum(pAig); j++){
            if (i == j)
                Lits[4 + j] = toLitCond(Vec_IntGetEntry(iVarEn, j), 1);
            else
                Lits[4 + j] = toLitCond(Vec_IntGetEntry(iVarEn, j), 0);
        }
        Lits[2] = toLitCond(pCnfPos->pVarNums[Aig_ObjId(pObj)], 0);
        Lits[3] = toLitCond(pCnfNeg->pVarNums[Aig_ObjId(pObj)], 1);

        // check positive unate
        Lits[0] = toLitCond(pCnfPos->pVarNums[Aig_ObjId(Aig_ManCo(pAig, 0))], 1);
        Lits[1] = toLitCond(pCnfNeg->pVarNums[Aig_ObjId(Aig_ManCo(pAig, 0))], 0);
        status = sat_solver_solve(pSat, Lits, Lits+(Aig_ManCiNum(pAig)+4), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
        if (status == l_False) // UNSAT
            isPosUnate = 1;

        // check negative unate
        Lits[0] = toLitCond(pCnfPos->pVarNums[Aig_ObjId(Aig_ManCo(pAig, 0))], 0);
        Lits[1] = toLitCond(pCnfNeg->pVarNums[Aig_ObjId(Aig_ManCo(pAig, 0))], 1);
        status = sat_solver_solve(pSat, Lits, Lits+(Aig_ManCiNum(pAig)+4), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
        if (status == l_False) // UNSAT
            isNegUnate = 1;
        
        if (isPosUnate && isNegUnate)
            Vec_IntPush(unateAigCi, 0);
        else if (isPosUnate)
            Vec_IntPush(unateAigCi, 1);
        else if (isNegUnate)
            Vec_IntPush(unateAigCi, 2);
        else
            Vec_IntPush(unateAigCi, 3);  
    }
    delete Lits;
}

void poUnate(Abc_Ntk_t* pNtk, Abc_Obj_t* po)
{
    int i, j;
    sat_solver * pSat;
    Abc_Obj_t * pObj;
    Vec_Int_t * posUnatePi = Vec_IntAlloc(0);
    Vec_Int_t * negUnatePi = Vec_IntAlloc(0);
    Vec_Int_t * binatePi = Vec_IntAlloc(0);
    Vec_Bit_t * inConePi = Vec_BitAlloc(Abc_NtkPiNum(pNtk)); // 1: in cone
    for (i = 0; i < Abc_NtkPiNum(pNtk); i++)
        Vec_BitPush(inConePi, 0);

    Abc_Ntk_t * cone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(po), Abc_ObjName(po), 0);
    // check if a pi is in cone
    j = 0;
    Abc_NtkForEachPi(pNtk, pObj, i){
        if (j < Abc_NtkPiNum(cone))
            if (!strcmp(Abc_ObjName(pObj), Abc_ObjName(Abc_NtkPi(cone, j)))){
                Vec_BitWriteEntry(inConePi, i, 1);
                j++;
            }
    }
    // Abc_Obj_t * pObj2;
    // Abc_NtkForEachPi(pNtk, pObj, i){
    //     Abc_NtkForEachPi(cone, pObj2, j){
    //         if (!strcmp(Abc_ObjName(pObj), Abc_ObjName(pObj2))){
    //             Vec_BitWriteEntry(inConePi, i, 1);
    //         }
    //     }
    // }
    
    Aig_Man_t * pAig = Abc_NtkToDar(cone, 0, 0);
    Cnf_Dat_t * pCnfPos = Cnf_Derive(pAig, Aig_ManCoNum(pAig));
    Cnf_Dat_t * pCnfNeg = Cnf_DataDup(pCnfPos);
    Cnf_DataLift(pCnfNeg, pCnfPos->nVars);

    Vec_Int_t * iVarEn = Vec_IntAlloc(Aig_ManCiNum(pAig));
    pSat = sat_solver_new();
    addClause(pSat, pAig, pCnfPos, pCnfNeg, iVarEn);

    // solve each pi
    Vec_Int_t * unateAigCi = Vec_IntAlloc(Aig_ManCiNum(pAig)); // 0: pos, 1: pos, 2: neg, 3: bi
    poUnateSolve(pSat, pAig, pCnfPos, pCnfNeg, iVarEn, unateAigCi);

    j = 0;
    Abc_NtkForEachPi(pNtk, pObj, i){
        if (Vec_BitGetEntry(inConePi, i)){
            if (Vec_IntGetEntry(unateAigCi, j) == 0){
                Vec_IntPush(posUnatePi, Abc_ObjId(pObj));
                Vec_IntPush(negUnatePi, Abc_ObjId(pObj));
            }
            else if (Vec_IntGetEntry(unateAigCi, j) == 1)
                Vec_IntPush(posUnatePi, Abc_ObjId(pObj));
            else if (Vec_IntGetEntry(unateAigCi, j) == 2)
                Vec_IntPush(negUnatePi, Abc_ObjId(pObj));
            else
                Vec_IntPush(binatePi, Abc_ObjId(pObj));
            j++;
        }
        else{
            Vec_IntPush(posUnatePi, Abc_ObjId(pObj));
            Vec_IntPush(negUnatePi, Abc_ObjId(pObj));
        }
    }

    sat_solver_delete(pSat);

    if (Abc_ObjFaninC0(po))
        printUnate(pNtk, po, negUnatePi, posUnatePi, binatePi);
    else
        printUnate(pNtk, po, posUnatePi, negUnatePi, binatePi);

    Vec_IntFree(posUnatePi);
    Vec_IntFree(negUnatePi);
    Vec_IntFree(binatePi);
    Vec_IntFree(iVarEn);
    Vec_IntFree(unateAigCi);
    Vec_BitFree(inConePi);
}

int pounate_Command(Abc_Frame_t *pAbc, int argc, char **argv)
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t* pObj;
    if (!Abc_NtkIsStrash(pNtk))
    {
        cout << "[error]The network should be in AIGs." << endl;
        return -1;
    }

    int i;
    Abc_NtkForEachPo(pNtk, pObj, i){
        poUnate(pNtk, pObj);
    }

    return 0;
} // namespace

// called during ABC startup
void init(Abc_Frame_t *pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", sopunate_Command, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", pounate_Command, 0);
}

// called during ABC termination
void destroy(Abc_Frame_t *pAbc)
{
}

// this object should not be modified after the call to Abc_FrameAddInitializer
Abc_FrameInitializer_t frame_initializer = {init, destroy};

// register the initializer a constructor of a global object
// called before main (and ABC startup)
struct registrar
{
    registrar()
    {
        Abc_FrameAddInitializer(&frame_initializer);
    }
} sopunate_registrar;

} // unnamed namespace
