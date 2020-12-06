#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <iostream>
#include <stdlib.h>
#include <vector>
#include <algorithm>
#include "sat/cnf/cnf.h"
#include "proof/pdr/pdrInt.h"
using namespace std;

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern "C" void * Cnf_DataWriteIntoSolver( Cnf_Dat_t * p, int nFrames, int fInit );

#define POS 0
#define NEG 1
#define SAT 1
#define UNSAT -1

namespace
{

void printAigObjInfo(Aig_Man_t* aigMan){	
    //print aigObj info
    Aig_Obj_t* aigObj;
    int i;
	cout << "**********************************************" << endl;
    Aig_ManForEachObj(aigMan, aigObj, i){
        cout << "ID: " << Aig_ObjId(aigObj) << endl;
        cout << "Type: " << Aig_ObjType(aigObj) << endl;
        cout << "FaininId0: " << Aig_ObjFaninId0(aigObj) << endl;
        cout << "FaininId1: " << Aig_ObjFaninId1(aigObj) << endl;
        cout << "FaininC0: " << Aig_ObjFaninC0(aigObj) << endl;
        cout << "FaininC1: " << Aig_ObjFaninC1(aigObj) << endl;
        cout << "Lit: " << Aig_ObjToLit(aigObj) << endl;
        cout << endl;
    }
	
	cout << "print Ci" << endl;
	Aig_ManForEachCi(aigMan, aigObj, i ){
		cout << "ID: " << Aig_ObjId(aigObj) << endl;
		cout << "Lit: " << Aig_ObjToLit(aigObj) << endl;
	}

	cout << "print Co" << endl;
    Aig_ManForEachCo(aigMan, aigObj, i ){
        cout << "ID: " << Aig_ObjId(aigObj) << endl;
        cout << "Lit: " << Aig_ObjToLit(aigObj) << endl;
    }

	cout << "**********************************************" << endl;

}

void printAigStatus(Aig_Man_t* aigMan){
    // print aig status
    cout << "aigMan: " << endl;
    Aig_ManPrintStats(aigMan);
    cout << endl;

    cout << "aigObj" << endl;
    printAigObjInfo(aigMan);
    cout << endl;
}

void printCnf(Cnf_Dat_t* ntkCnf){
    //print cnf
	cout << "**********************************************" << endl;
	cout << ntkCnf->pMan->pName << endl;
	cout << "number of variables = " << ntkCnf->nVars << endl;
    cout << "number of literals = " << ntkCnf->nLiterals << endl;
    cout << "number of clauses = " << ntkCnf->nClauses << endl;
    int *pBeg, *pEnd;
	int i;
    Cnf_CnfForClause(ntkCnf, pBeg, pEnd, i ){
        for(int* pLit = pBeg; pLit != pEnd; ++pLit){
            cout << (Abc_LitIsCompl(*pLit)? "-": "") << Abc_Lit2Var(*pLit) << " ";
        }
        cout << endl;
    }
}

void printCiInfo(Abc_Obj_t* nodeCi){
	cout << "ID: " << Abc_ObjId(nodeCi) << endl;
	cout << "name: " << Abc_ObjName(nodeCi) << endl;
}
/*
Abc_Ntk_t* get1OutputNtk(Abc_Ntk_t* abcNtk, Abc_Obj_t* nodeCo){


}
*/

//main function
int Lsv_CommandPrintPOUnate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
	Abc_Ntk_t* abcNtk = Abc_FrameReadNtk(pAbc);
	Abc_Ntk_t* abcNtk_1Po;
	Abc_Obj_t* nodeCo;

	int i;
	int fUseAllCis = 1;
	Abc_NtkForEachPo( abcNtk, nodeCo, i ) {
		//get single output abc_ntk
		abcNtk_1Po = Abc_NtkCreateCone( abcNtk, Abc_ObjFanin0(nodeCo), Abc_ObjName(nodeCo), fUseAllCis );
		
		//check output negative
		if (Abc_ObjFaninC0(nodeCo) ){
			Abc_NtkPo(abcNtk_1Po, 0)->fCompl0  ^= 1;
		}

		/*
		//for debug
		Abc_Obj_t* nodeCi;
		int j;
		Abc_NtkForEachPi(abcNtk, nodeCi, j){
			printCiInfo(nodeCi);
		}
		//
		*/
		
		//get aig
		Aig_Man_t* aigMan   = Abc_NtkToDar(abcNtk_1Po, 0, 0);
		//aigMan->pData = NULL;

/*		
		//for debug
		cout << endl << "print aig: " << endl;
        printAigObjInfo(aigMan);
        cout << endl;
*/		
	
		//get cnf
		Cnf_Dat_t* ntkCnf = Cnf_Derive( aigMan, Aig_ManCoNum(aigMan) );
		Vec_Int_t * vCiIds = Cnf_DataCollectPiSatNums( ntkCnf, aigMan );
		//printCnf(ntkCnf);

		/*
		//for debug
		cout << "pVarNums:" << endl;
		for(int i = 0; i < aigMan->vObjs->nSize; ++i){
			cout << "abcObjID = " << i << endl;
			cout << "cnfVar = " << ntkCnf->pVarNums[i] << endl;
		}
		*/

		//init sat solver by adding F CNF 
		sat_solver* satSol = (sat_solver*)Cnf_DataWriteIntoSolver(ntkCnf, 1, 0);
		if ( satSol == NULL ){
			cout << "Error! SAT solver is null" << endl;
            continue;
        }
/*
		//for adding constrain
		int *pLits = ABC_ALLOC(int, 1);

		//add F output constrain;
		Aig_Obj_t *  aigCo = Aig_ManCo( aigMan, 0 );
		pLits[0] = toLitCond(ntkCnf->pVarNums[Aig_ObjId(aigCo)], POS); 
		cout << "F po = " << pLits[0] << endl;
		if ( !sat_solver_addclause( satSol, pLits, pLits + 1 )){
            cout << "error in adding output constrain to sat solver" << endl;
			continue;
        }
*/

		//create my constrain
		
		// create F'
		int latest_var_num = ntkCnf->nVars - 1;
		//cout << "latest_var_num = " << latest_var_num << endl;
		int *pBeg, *pEnd;
	    int i;
		cout << "CNF of F:" << endl;
		Cnf_CnfForClause(ntkCnf, pBeg, pEnd, i ){
			for(int* pLit = pBeg; pLit != pEnd; ++pLit){
				cout << (Abc_LitIsCompl(*pLit)? "-": "") << Abc_Lit2Var(*pLit) << " ";
			}
			cout << endl;
		}

		cout << "CNF of F':" << endl;
		Cnf_CnfForClause(ntkCnf, pBeg, pEnd, i ){
			int nLits = pEnd - pBeg; 
			int *one_clause = ABC_ALLOC(int, nLits);
            for(int* pLit = pBeg; pLit != pEnd; ++pLit){
				one_clause[pLit - pBeg] = toLitCond(Abc_Lit2Var(*pLit) + latest_var_num, Abc_LitIsCompl(*pLit));
			}
			if ( !sat_solver_addclause( satSol, one_clause, one_clause + nLits ) ){
			    cout << "error in adding output constrain to sat solver" << endl;
		        continue;
	        }
			//print for debug
			for(int idx = 0; idx < nLits; ++idx){
                cout << (Abc_LitIsCompl(one_clause[idx])? "-": "") << Abc_Lit2Var(one_clause[idx]) << " ";
            }
            cout << endl;
        }

		//for adding (F' + F) constrain
        int *pLits = ABC_ALLOC(int, 2);
        int poVar = ntkCnf->pVarNums[Aig_ObjId(Aig_ManCo(aigMan, 0) )]; 
		cout << "poVar = " << poVar << endl;
        pLits[0] = toLitCond(poVar, POS);
		pLits[1] = toLitCond(poVar + latest_var_num, NEG);
        cout << "add clause: " << pLits[0] << " + " << pLits[1] << endl;
        if ( !sat_solver_addclause( satSol, pLits, pLits + 2 )){
            cout << "error in adding output constrain to sat solver" << endl;
            continue;
        }



		//

		//simplify the problem
		int status = sat_solver_simplify(satSol);
		if ( status == 0 ){
            printf( "The problem is UNSATISFIABLE after simplification.\n" );
			sat_solver_delete( satSol );
	        Vec_IntFree( vCiIds );
		    Cnf_DataFree(ntkCnf);
			Aig_ManStop(aigMan);
			Abc_NtkDelete(abcNtk_1Po);
            continue;
        }

		//solve sat 
		status = sat_solver_solve( satSol, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
		
		//result
		if ( status == SAT ){
            printf( "The problem is SATISFIABLE.\n" );

			//get cex assignment
			aigMan->pData = Sat_SolverGetModel( satSol, vCiIds->pArray, vCiIds->nSize );
			abcNtk_1Po->pModel = (int *)aigMan->pData;

			//check
			int * pSimInfo = Abc_NtkVerifySimulatePattern( abcNtk_1Po, abcNtk_1Po->pModel );
	        if ( pSimInfo[0] != 1 )
				Abc_Print( 1, "ERROR in Abc_NtkMiterSat(): Generated counter example is invalid.\n" );
			ABC_FREE( pSimInfo );
		   
			//create cex
			pAbc->pCex = Abc_CexCreate( 0, Abc_NtkPiNum(abcNtk_1Po), abcNtk_1Po->pModel, 0, 0, 0 );
			//Abc_CexPrint( pAbc->pCex );
		
		}
        else if ( status == UNSAT ){
			printf( "The problem is UNSATISFIABLE.\n" );
        }
		else{
			cout << "err in satsol!" << endl;
		}

		//free memory
		sat_solver_delete( satSol ); //cout << "ok to free sat" << endl;
		Vec_IntFree( vCiIds ); //cout << "ok to free vCiIds" << endl;
		Cnf_DataFree(ntkCnf); //cout << "ok to free CNF" << endl;
		Aig_ManStop(aigMan); //cout << "ok to free AIG" << endl;
		//Abc_NtkDelete(abcNtk_1Po); cout << "ok to free ntk" << endl;
	}
    return 0;
}

// called during ABC startup
void init(Abc_Frame_t* pAbc)
{
    Cmd_CommandAdd( pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPOUnate, 0);
}

// called during ABC termination
void destroy(Abc_Frame_t* pAbc)
{
}

// this object should not be modified after the call to Abc_FrameAddInitializer
Abc_FrameInitializer_t frame_initializer = { init, destroy };

// register the initializer a constructor of a global object
// called before main (and ABC startup)
struct registrar
{
    registrar() 
    {
        Abc_FrameAddInitializer(&frame_initializer);
    }
} myAdd_registrar;

} // unnamed namespace

