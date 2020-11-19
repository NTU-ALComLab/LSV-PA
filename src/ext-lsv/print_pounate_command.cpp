#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <iostream>
#include <stdlib.h>
#include <vector>
#include <algorithm>
using namespace std;

namespace
{

int Lsv_CommandPrintPOUnate( Abc_Frame_t * pAbc, int argc, char ** argv )
{
	cout << "successfully add new command: print_pounate" << endl;
	/*
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t* pObj;

	int i;
	Abc_NtkForEachNode(pNtk, pObj, i) {
	//	cout << "node " << Abc_ObjName(pObj) << ":" << endl;

		if (Abc_NtkHasSop(pNtk)) {
			string str((char*)pObj->pData);
			
			cout << "-------------------------" << endl;
			cout << str; 
			cout << "-------------------------" << endl;
			
		}//end if sop
	}//end for each node
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
