#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <iostream>
#include <stdlib.h>
#include <vector>
#include <algorithm>
#include "sat/cnf/cnf.h"
using namespace std;

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

namespace
{

int Lsv_CommandPrintPOUnate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
	Abc_Ntk_t* abcNtk = Abc_FrameReadNtk(pAbc);
	Aig_Man_t* aigMan	= Abc_NtkToDar( abcNtk, 0, 0 );
	
	cout << "aigMan: " << endl;
	Aig_ManPrintStats(aigMan);
	cout << endl;
	
	Cnf_Dat_t* ntkCnf = Cnf_Derive( aigMan, Aig_ManCoNum(aigMan) );
	//Cnf_Man_t* cnfMan = Cnf_ManRead();

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

	int *pBeg, *pEnd;
	Cnf_CnfForClause(ntkCnf, pBeg, pEnd, i ){
		for(int* pLit = pBeg; pLit != pEnd; ++pLit){
			cout << (Abc_LitIsCompl(*pLit)? "-": "") << Abc_Lit2Var(*pLit) << " ";
		}
		cout << endl;
	}
	//sat_solver2 * pSat = (sat_solver2 *)Cnf_DataWriteIntoSolver2( pCnf, 1, 0 );	
/*
	Aig_ManForEachCo(aigMan, aigObj, i ){
		cout << "ID: " << Aig_ObjId(aigObj) << endl;
		cout << "FaininId0: " << Aig_ObjFaninId0(aigObj) << endl;
		cout << "FaininId1: " << Aig_ObjFaninId1(aigObj) << endl;
		//Cnf_CutPrint(aigObj->pData);

		//Cnf_Cut_t* cnfCut = Cnf_CutCreate(cnfMan, Aig_ObjChild0(aigObj));
		//Cnf_CutPrint(cnfCut);
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
