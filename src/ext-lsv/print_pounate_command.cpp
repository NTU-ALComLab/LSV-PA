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

namespace
{

void printAigObjInfo(Aig_Man_t* aigMan){	
    //print aigObj info
    Aig_Obj_t* aigObj;
    int i;
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
	cout << ntkCnf->pMan->pName << endl;
    int *pBeg, *pEnd;
	int i;
    Cnf_CnfForClause(ntkCnf, pBeg, pEnd, i ){
        for(int* pLit = pBeg; pLit != pEnd; ++pLit){
            cout << (Abc_LitIsCompl(*pLit)? "-": "") << Abc_Lit2Var(*pLit) << " ";
        }
        cout << endl;
    }
}



int Lsv_CommandPrintPOUnate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
	Abc_Ntk_t* abcNtk = Abc_FrameReadNtk(pAbc);
	Abc_Ntk_t* abcNtk_1Po;
	Abc_Obj_t* nodeCo;

	int i;
	int fUseAllCis = 1;
	Abc_NtkForEachPo( abcNtk, nodeCo, i ) {
		abcNtk_1Po = Abc_NtkCreateCone( abcNtk, Abc_ObjFanin0(nodeCo), Abc_ObjName(nodeCo), fUseAllCis );
		
		if (Abc_ObjFaninC0(nodeCo) ){
			Abc_NtkPo(abcNtk_1Po, 0)->fCompl0  ^= 1;
		}
		Aig_Man_t* aigMan   = Abc_NtkToDar(abcNtk_1Po, 0, 0);
		Cnf_Dat_t* ntkCnf = Cnf_Derive( aigMan, Aig_ManCoNum(aigMan) );
	
		//sat solver
		sat_solver* satSol = (sat_solver*)Cnf_DataWriteIntoSolver(ntkCnf, 1, 0);
		if ( satSol == NULL ){
            Cnf_DataFree( ntkCnf );
            return 1;
        }
		
		Vec_Int_t * vCiIds = Cnf_DataCollectPiSatNums( ntkCnf, aigMan );
		Cnf_DataFree(ntkCnf);
		int status = sat_solver_simplify(satSol);
		if ( status == 0 ){
            Vec_IntFree( vCiIds );
            sat_solver_delete( satSol );
            printf( "The problem is UNSATISFIABLE after simplification.\n" );
            return 1;
        }

		status = sat_solver_solve( satSol, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
		if ( status == 1 ){
            printf( "The problem is SATISFIABLE.\n" );
			//cex
			aigMan->pData = Sat_SolverGetModel( satSol, vCiIds->pArray, vCiIds->nSize );
			Sat_SolverPrintStats( stdout, satSol );
			sat_solver_delete( satSol );
	        Vec_IntFree( vCiIds );

			abcNtk->pModel = (int *)aigMan->pData, aigMan->pData = NULL;
			//check
			int * pSimInfo = Abc_NtkVerifySimulatePattern( abcNtk, abcNtk->pModel );
	        if ( pSimInfo[0] != 1 )
				Abc_Print( 1, "ERROR in Abc_NtkMiterSat(): Generated counter example is invalid.\n" );
			ABC_FREE( pSimInfo );
		    
			pAbc->pCex = Abc_CexCreate( 0, Abc_NtkPiNum(abcNtk), abcNtk->pModel, 0, 0, 0 );
			pAbc->Status = 0;
			Abc_CexPrint( pAbc->pCex );
		
		}
        else if ( status == -1 ){
			pAbc->Status = 1;
            printf( "The problem is UNSATISFIABLE.\n" );
        }
		else{
			cout << "err in satsol!" << endl;
		}



	}








	//Aig_Man_t* aigMan	= Abc_NtkToDar( abcNtk, 0, 0 );
	
	/*
	//print cnf
	Cnf_Dat_t* ntkCnf = Cnf_Derive( aigMan, Aig_ManCoNum(aigMan) );
	int *pBeg, *pEnd;
	Cnf_CnfForClause(ntkCnf, pBeg, pEnd, i ){
		for(int* pLit = pBeg; pLit != pEnd; ++pLit){
			cout << (Abc_LitIsCompl(*pLit)? "-": "") << Abc_Lit2Var(*pLit) << " ";
		}
		cout << endl;
	}
	*/
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
