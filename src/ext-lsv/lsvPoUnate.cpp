#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"

#include <iostream>
#include <queue>
#include <vector>
#include <algorithm>
#include <functional>

using namespace std;

namespace pounate{ 

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef pair<int, Abc_Obj_t* > IdObj;
typedef priority_queue< IdObj, vector<IdObj>, greater<IdObj> > IdObjQueue;


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv);
static void Lsv_NtkPrintPoUnate(Abc_Ntk_t* pNtk); 

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

void record_pio_var(Cnf_Dat_t *pCnf, vector<int> &vpi, vector<int> &vpo){
    Aig_Obj_t * pObj; int i=0;
    Aig_ManForEachCi( pCnf->pMan, pObj, i )
    {
        if ( pCnf->pVarNums[pObj->Id] >= 0 )
            vpi.push_back( pCnf->pVarNums[pObj->Id] );
    }
    Aig_ManForEachCo( pCnf->pMan, pObj, i )
    {
        if ( pCnf->pVarNums[pObj->Id] >= 0 )
            vpo.push_back( pCnf->pVarNums[pObj->Id] );    
    }
}

void connect_pi(sat_solver *pSat, vector<int>& posCofPiList, vector<int>& negCofPiList, vector<int>& disableList){
    
    lit Lits[3];

    for(int i=0; i< posCofPiList.size(); ++i){

        disableList.push_back(sat_solver_addvar(pSat)); // ax

        // (~ax + x <-> x')
        Lits[0] = toLitCond( posCofPiList[i], 0 ); // x
        Lits[1] = toLitCond( negCofPiList[i], 1 ); // ~x'
        Lits[2] = toLitCond( disableList[i],  1);  // ~ax
        sat_solver_addclause( (sat_solver *)pSat, Lits, Lits + 3 );          

        Lits[0] = toLitCond( posCofPiList[i], 1 ); // ~x
        Lits[1] = toLitCond( negCofPiList[i], 0 ); // x'
        Lits[2] = toLitCond( disableList[i],  1);  // ~ax
        sat_solver_addclause( (sat_solver *)pSat, Lits, Lits + 3 );            
    } 
    
}

sat_solver * construct_CNF(Aig_Man_t * pMan, vector<int>& posCofPoList, vector<int>& negCofPoList, 
                   vector<int>& posCofPiList, vector<int>& negCofPiList, vector<int>& disableList ){
    
    pMan->pData = NULL;
    
    // derive CNF for positive cofactor circuit
    Cnf_Dat_t * pCnf= Cnf_Derive( pMan, Aig_ManCoNum(pMan) );

    //record Pi var num and Po var num for positive cofactor circuit
    record_pio_var(pCnf, posCofPiList, posCofPoList);

    // write cnf into SAT solver
    sat_solver *pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf, 1, 0 );

    // rename CNF variable for negative cofactor circuit
    Cnf_DataLift( pCnf, pCnf->nVars );
    
    //record Pi var num and Po var num for negative cofactor circuit
    record_pio_var(pCnf, negCofPiList, negCofPoList);
    assert(posCofPiList.size()==negCofPiList.size()); 
    assert(posCofPoList.size()==negCofPoList.size());

    // write the variable-renamed cnf into SAT solver
    for ( int i = 0; i < pCnf->nClauses; ++i )
        sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1]);
    
    //connect the two circuits
    connect_pi(pSat, posCofPiList, negCofPiList, disableList);

    Cnf_DataFree( pCnf );
    
    return pSat;
}


void resetUnateVec(vector<int>& UnateVec){
    //reset the content of UnateVec to binary value:11
    fill(UnateVec.begin(), UnateVec.end(),3);     
}

void test_unate( int i, sat_solver *pSat, vector<int>& UnateVec, int posPo, int negPo, int isNeg,
                 lit* assumpList, int assumpSize ){
        
        //check for positive unate, F~x -> Fx,  check F~x ^ ~Fx unsat
        //check for negative unate  Fx -> F~x,  check Fx ^ ~F~x unsat
        assumpList[assumpSize-2] = toLitCond(posPo, 1^isNeg);
        assumpList[assumpSize-1] = toLitCond(negPo, 0^isNeg); 

        int status = sat_solver_solve( pSat,assumpList, assumpList+assumpSize, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        if ( status == l_False ) //unsat
            UnateVec[i] &= (1 << isNeg); 
}

void setUnateVec( sat_solver *pSat, vector<int>& UnateVec, int posPo, int negPo, vector<int>& posCofPiList, 
                  vector<int>& negCofPiList, vector<int>& disableList, lit* assumpList, int assumpSize ){
    
    for(int i=0;i< posCofPiList.size(); ++i) 
        assumpList[i] = toLitCond(disableList[i], 0); // ax=1 force x<->x'
 
    for(int i=0; i< posCofPiList.size(); ++i){
        //set ax
        assumpList[i] = toLitCond(disableList[i], 1); // ax=0 
        assumpList[assumpSize-4] = toLitCond(posCofPiList[i],0); // x =1
        assumpList[assumpSize-3] = toLitCond(negCofPiList[i],1); // x'=0
        
        //test positive unate
        test_unate( i, pSat, UnateVec, posPo, negPo, 0 , assumpList, assumpSize );         
        //test negative unate
        test_unate( i, pSat, UnateVec, posPo, negPo, 1 , assumpList, assumpSize ); 
        //reset ax
        assumpList[i] = toLitCond(disableList[i], 0); // ax=1 force x<->x'

    }
}

void print_unate( Abc_Ntk_t * pNtk, vector<int>& UnateVec, int n){
    //n=1: pos, n=2: neg, n=3: bi
    bool occur=false;
    for(int i=0; i< UnateVec.size(); ++i){
        if(!occur && (UnateVec[i] == n || ( n!= 3 && UnateVec[i] == 0 ) ) ){
            cout<< ( (n == 3) ? "binate inputs:" : ( (n==2) ? "-unate inputs:" : "+unate inputs:" ) );
            printf(" %s",Abc_ObjName(Abc_NtkPi(pNtk,i) ) );
            occur = true;
        }
        else if(occur && (UnateVec[i] == n || ( n!= 3 && UnateVec[i] == 0 ) ) )
            printf(",%s",Abc_ObjName(Abc_NtkPi(pNtk,i) ) );
    }
    if(occur) printf("\n");
}

extern "C"{
void Lsv_NtkPrintPoUnate(Abc_Ntk_t* pNtk) {
    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkLatchNum(pNtk) == 0 );

    //create Aig manager
    extern  Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters ); 
    Aig_Man_t * pMan = Abc_NtkToDar( pNtk, 0, 0 );

    //construct cnf 
    sat_solver * pSat;
    vector<int> posCofPoList, negCofPoList, posCofPiList, negCofPiList, disableList; //store cnf var num 
    pSat = construct_CNF(pMan, posCofPoList, negCofPoList, posCofPiList, negCofPiList, disableList);

    //assumption list
    int assumpSize = posCofPiList.size()+4;
    lit* assumpList = new lit [ assumpSize ];

    vector<int> UnateVec(Abc_NtkPiNum(pNtk),3);
    // Encode:
    // 11: binate 
    // 00: positive and negative unate
    // 01: positive unate
    // 10: negative unate

    //sort by pair( Id, Abc_Obj_t* )
    //IdObjQueue PosQueue, NegQueue, BiQueue; 
    
    Abc_Obj_t* pObj; int i;
    Abc_NtkForEachPo(pNtk, pObj, i) {
        
        //determine the po's unateness with respect to all pis
        resetUnateVec(UnateVec); 
        setUnateVec( pSat, UnateVec, posCofPoList[i], negCofPoList[i] , posCofPiList, 
                     negCofPiList,disableList, assumpList, assumpSize );
        
        printf("node %s:\n", Abc_ObjName(pObj));
        //print pos unate
        print_unate( pNtk, UnateVec, 1);
        //print neg unate
        print_unate( pNtk, UnateVec, 2);
        //print binate
        print_unate( pNtk, UnateVec, 3);
        
    }

    delete [] assumpList;
    sat_solver_delete( pSat );
    Aig_ManStop( pMan );
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
