#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"

#include <iostream>
#include <vector>
#include <algorithm>
#include <string.h>

using namespace std;

namespace pounate{ 

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

#define NOTUSED -2
#define INIT -1
#define BINATE 3
#define POS 1
#define NEG 2
#define BOTH 0

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv);

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

void init(Abc_Frame_t* pAbc) {
   Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPoUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

void record_pio_var(Cnf_Dat_t *pCnf, vector<int>& vpis, int& vpo){
    
    Aig_Obj_t * pObj; int i=0, k=0;
    //Pi
    Aig_ManForEachCi( pCnf->pMan, pObj, i )
    {
        assert( pCnf->pVarNums[pObj->Id] >= 0 );
        while(vpis[k] == NOTUSED) k++;
        assert(vpis[k] == INIT);
        vpis[k] = pCnf->pVarNums[pObj->Id] ;
        k++;
    }
    //Po
    assert( Aig_ManCoNum(pCnf->pMan) == 1 );
    pObj = Aig_ManCo( pCnf->pMan, 0 ); 
    assert( pCnf->pVarNums[pObj->Id] >= 0 );
    vpo = pCnf->pVarNums[pObj->Id] ;    
}

void connect_pi(sat_solver *pSat, vector<int>& posCofPiVars, int VarShift, vector<int>& ForceEqVars ){
      
    lit Lits[3];
    assert(ForceEqVars.size()== posCofPiVars.size());
    for(int i=0; i< posCofPiVars.size(); ++i){
        if(posCofPiVars[i] == NOTUSED) 
            assert(ForceEqVars[i] == NOTUSED);
        else{
            assert(ForceEqVars[i] != NOTUSED && posCofPiVars[i]>=0 );
            ForceEqVars[i] = sat_solver_addvar(pSat); // ax

            // (~ax + x <-> x')
            Lits[0] = toLitCond( posCofPiVars[i], 0 ); // x
            Lits[1] = toLitCond( posCofPiVars[i]+VarShift, 1 ); // ~x'
            Lits[2] = toLitCond( ForceEqVars[i],  1);  // ~ax
            sat_solver_addclause( (sat_solver *)pSat, Lits, Lits + 3 );          

            Lits[0] = toLitCond( posCofPiVars[i], 1 ); // ~x
            Lits[1] = toLitCond( posCofPiVars[i]+VarShift, 0 ); // x'
            Lits[2] = toLitCond( ForceEqVars[i], 1);  // ~ax
            sat_solver_addclause( (sat_solver *)pSat, Lits, Lits + 3 );            
        }
    } 
}

sat_solver * construct_CNF(Aig_Man_t * pMan, int& posCofPoVar, vector<int>& posCofPiVars, 
                           int& negCofVarShift, vector<int>& ForceEqVars){

    pMan->pData = NULL;
    
    // derive CNF for positive cofactor circuit
    Cnf_Dat_t * pCnf= Cnf_Derive( pMan, Aig_ManCoNum(pMan) );

    //record Pi var num and Po var num for positive cofactor circuit
    record_pio_var(pCnf, posCofPiVars, posCofPoVar);
    
    // write cnf into SAT solver
    sat_solver *pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );

    // rename CNF variable for negative cofactor circuit
    assert(negCofVarShift==0);
    negCofVarShift = pCnf->nVars;
    Cnf_DataLift( pCnf, pCnf->nVars );
    
    // write the variable-renamed cnf into SAT solver
    for ( int i = 0; i < pCnf->nClauses; ++i )
        sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1]);
    
    //connect the two circuits
    connect_pi(pSat, posCofPiVars, negCofVarShift, ForceEqVars);

    Cnf_DataFree( pCnf );
    
    return pSat;
}


void resetVec(vector<int>& Vec, int v){
    //reset the content of UnateVec to binary value:11
    fill(Vec.begin(), Vec.end(),v);     
}

void test_unate( int i, sat_solver *pSat, vector<int>& UnateVec, int posCofPoVar, int VarShift, int isNeg,
                 lit* assumpList, int assumpSize ){
        
        //check for positive unate, F~x -> Fx,  check F~x ^ ~Fx unsat
        //check for negative unate  Fx -> F~x,  check Fx ^ ~F~x unsat
        assumpList[assumpSize-2] = toLitCond( posCofPoVar, 1^isNeg);
        assumpList[assumpSize-1] = toLitCond( posCofPoVar+VarShift, 0^isNeg); 

        int status = sat_solver_solve( pSat,assumpList, assumpList+assumpSize, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        if ( status == l_False ) //unsat
            UnateVec[i] &= (1 << isNeg); 
}

int init_assump( vector<int>& posCofPiVars, vector<int>& ForceEqVars, lit* assumpList){

    int k=0; 
    for(int i=0;i< posCofPiVars.size(); ++i){ 
        if(posCofPiVars[i]!= NOTUSED){
            assert( posCofPiVars[i]>=0 && ForceEqVars[i] >=0);
            assumpList[k++] = toLitCond(ForceEqVars[i], 0); // ax=1 force x<->x'
        }
        else assert(ForceEqVars[i] == NOTUSED);
    }
    return k+4;

}

void setUnateVec( sat_solver *pSat, vector<int>& UnateVec, int posCofPoVar, vector<int>& posCofPiVars, 
                  int VarShift, vector<int>& ForceEqVars, lit* assumpList){
   
    //set assumption list and assumption size
    int assumpSize = init_assump( posCofPiVars, ForceEqVars, assumpList);

    int k=0;
    for(int i=0; i< posCofPiVars.size(); ++i){
        if(posCofPiVars[i]!= NOTUSED ){
            //set ax
            assumpList[k] = toLitCond( ForceEqVars[i], 1); // ax=0 
            assumpList[assumpSize-4] = toLitCond( posCofPiVars[i], 0); // x =1
            assumpList[assumpSize-3] = toLitCond( posCofPiVars[i]+VarShift, 1); // x'=0
            
            //test positive unate
            test_unate( i, pSat, UnateVec, posCofPoVar, VarShift, 0 , assumpList, assumpSize );         
            //test negative unate
            test_unate( i, pSat, UnateVec, posCofPoVar, VarShift, 1 , assumpList, assumpSize ); 
            //reset ax
            assumpList[k++] = toLitCond(ForceEqVars[i], 0); // ax=1 force x<->x'
        }
        else
            UnateVec [i] = BOTH; //both positive and negative unate

    }
}

void print_unate( Abc_Ntk_t * pNtk, vector<int>& UnateVec, int n){
    //n=1: pos, n=2: neg, n=3: bi
    bool occur=false;
    for(int i=0; i< UnateVec.size(); ++i){
        if  (UnateVec[i] == n || ( n!= BINATE && UnateVec[i] == BOTH ) ){
            if(!occur){
                cout<< ( (n == BINATE) ? "binate inputs:" : ( ( n == NEG ) ? "-unate inputs:" : "+unate inputs:" ) );
                printf(" %s",Abc_ObjName(Abc_NtkPi(pNtk,i) ) );
                occur = true;
            }
            else
                printf(",%s",Abc_ObjName(Abc_NtkPi(pNtk,i) ) );
        }
    }
    if(occur) printf("\n");
}

void set_nonused_pi( Abc_Ntk_t * pNtk, Abc_Ntk_t * pNtkPo, vector<int>& posCofPiVars, vector<int>& ForceEqVars){

    int j=0, k=0;
    int piNum = Abc_NtkPiNum(pNtk);
    Abc_Obj_t *pNodePi;
    Abc_NtkForEachPi(pNtkPo, pNodePi, j ){
        assert( k < piNum );
        while( strcmp(Abc_ObjName( Abc_NtkPi(pNtk,k) ), Abc_ObjName( pNodePi )) !=0 ){
               //not equal
               posCofPiVars[k]= NOTUSED; //set not used flag 
               ForceEqVars[k++]= NOTUSED;
               assert( k< piNum );
        }
        k++;
    }
    for( ; k< piNum ; ++k){
        posCofPiVars[k]= NOTUSED; //set not used flag 
        ForceEqVars[k]= NOTUSED;
    }
}

extern "C"{
void Lsv_NtkPrintPoUnate(Abc_Ntk_t* pNtk) {
    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkLatchNum(pNtk) == 0 );

    extern  Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters ); 
    int piNum = Abc_NtkPiNum(pNtk);

    //store cnf variable num
    vector<int>  posCofPiVars(piNum, INIT), ForceEqVars(piNum, INIT);  
    int posCofPoVar=0, negCofVarShift=0;

    //assumption list
    lit* assumpList = new lit [ piNum+4 ];

    //represent the unateness of each pi
    vector<int> UnateVec(Abc_NtkPiNum(pNtk), BINATE);
    // Encode:
    // 11: binate 
    // 00: positive and negative unate
    // 01: positive unate
    // 10: negative unate

    Abc_Obj_t *pObj; int i; 
    Abc_NtkForEachPo(pNtk, pObj, i) {

        Abc_Ntk_t * pNtkPo = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pObj), Abc_ObjName(pObj), 0 );
        if ( Abc_ObjFaninC0(pObj) )
           Abc_ObjXorFaninC( Abc_NtkPo(pNtkPo, 0), 0 );
        Aig_Man_t * pMan = Abc_NtkToDar( pNtkPo, 0, 0 );
        assert( Aig_ManCoNum(pMan) == 1 );

        //set the nonused pi entry of posCofPiVars and ForceEqVar
        set_nonused_pi(pNtk, pNtkPo, posCofPiVars,ForceEqVars);

        //construct cnf 
        sat_solver * pSat = construct_CNF(pMan, posCofPoVar, posCofPiVars, negCofVarShift, ForceEqVars);

        //determine the po's unateness with respect to all pis
        setUnateVec( pSat, UnateVec, posCofPoVar, posCofPiVars, negCofVarShift, ForceEqVars, assumpList );

        printf("node %s:\n", Abc_ObjName(pObj));
        //print pos unate
        print_unate( pNtk, UnateVec, POS);
        //print neg unate
        print_unate( pNtk, UnateVec, NEG);
        //print binate
        print_unate( pNtk, UnateVec, BINATE);

        //reset
        posCofPoVar=0; negCofVarShift=0;
        resetVec(UnateVec, BINATE);
        resetVec(posCofPiVars, INIT);
        resetVec(ForceEqVars, INIT);
        Abc_NtkDelete( pNtkPo );
        Aig_ManStop( pMan );
        sat_solver_delete( pSat );
    }
}
}

int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv)
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
    Lsv_NtkPrintPoUnate(pNtk);
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_print_pounate [-h] <file> \n");
    Abc_Print(-2, "\t        prints the unateness of primary outputs in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}

}
