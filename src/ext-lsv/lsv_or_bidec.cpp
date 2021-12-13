#include <iostream>
#include <algorithm>
#include <string>
#include <vector>
#include <unordered_map>
#include "base/abc/abc.h"
#include "sat/cnf/cnf.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

using namespace std;

/*=== src/base/abci/abcDar.c ==========================================*/
extern "C"
{
    Aig_Man_t *  Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

// add new command
static int LSV_CommandOrBidec(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_or_bidec", LSV_CommandOrBidec, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = { init, destroy };

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// ** some useful function **
// abc.h --> Abc_ObjIsPi(pObj), Abc_ObjIsPo(pObj)
// abc.h --> Abc_ObjForEachFanin(), Abc_ObjForEachFanout()
// abc.h --> Abc_NtkForEachPi(), Abc_NtkForEachPo()


// main function
void Lsv_NtkOrBidec(Abc_Ntk_t* pNtk)
{
    // global variable 
    Abc_Obj_t* PO;
    Abc_Ntk_t* pNtk_support;
    sat_solver* pSat;
    int i;

    // For each PO, extract cone of each PO & support set
    Abc_NtkForEachPo(pNtk, PO, i)
    {
        // 1. Store support X as a circuit network 
            // Q1 : Abc_NtkCreateCone() 要吃進 PO ? Abc_ObjFanin0(PO) ?
            // Q2 : Abc_NtkStrash() 必要 ?
        pNtk_support = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(PO), Abc_ObjName(PO), 0);
        pNtk_support = Abc_NtkStrash(pNtk_support, 0, 0, 0);

        // 2. Derive equivalent "Aig_Man_t" from "Abc_Ntk_t"
        Aig_Man_t* pAig = Abc_NtkToDar(pNtk_support, 0, 0);

        // 3. Construct CNF formula --> f(X)
            // cnf.h --> struct Cnf_Daat_t_
        Cnf_Dat_t* pCNF = Cnf_Derive(pAig, 1);
        pSat = (sat_solver*) Cnf_DataWriteIntoSolver(pCNF, 1, 0);
            // Obtain "VarShift" by extracting the max varnum() in CNF
        for (int i = 0 ; i < pCNF->nLiterals ; ++i)
        {
            cout << "var " <<  i << " : " << pCNF->pVarNums << endl;
            // 15 nLiterals ; 6 nVars ; 15 nClauses
        }
        

    }


}


// Define command function : LSV_CommandOrBidec
int LSV_CommandOrBidec(Abc_Frame_t* pAbc, int argc, char** argv)
{
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF)
  {
    switch (c)
    {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk)
  {
    Abc_Print(-1, "Empty network.\n");
    return -1;
  }
  // main function
  Lsv_NtkOrBidec(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_or_bidec [-h]\n");
  Abc_Print(-2, "\t        check the OR bi-decomposition in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;

}