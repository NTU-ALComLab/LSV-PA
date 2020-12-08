#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "ext-lsv/lsvUtils.h"

static int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv);
extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

void init_PrintPoUnate(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPoUnate, 0);
}

void destroy_PrintPoUnate(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer_PrintPoUnate = {init_PrintPoUnate, destroy_PrintPoUnate};

struct PackageRegistrationManager_PrintPoUnate {
  PackageRegistrationManager_PrintPoUnate() { Abc_FrameAddInitializer(&frame_initializer_PrintPoUnate); }
} lsvPackageRegistrationManager_PrintPoUnate;


void Lsv_NtkPrintPoUnate(Abc_Ntk_t * pNtk) {
  Abc_Obj_t * pPo, * pPi;
  Abc_Ntk_t * pNtkCone;
  Aig_Man_t * pMan;
  int i, j;

  int PiNum = Abc_NtkPiNum( pNtk );
  Vec_Ptr_t * posUnateVec = Vec_PtrAlloc( PiNum );
  Vec_Ptr_t * negUnateVec = Vec_PtrAlloc( PiNum );
  Vec_Ptr_t * binateVec = Vec_PtrAlloc( PiNum );

  Abc_NtkForEachPo( pNtk, pPo, i ) {

    pNtkCone = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 1 );
    pMan = Abc_NtkToDar( pNtkCone, 0, 0 );
    Cnf_Dat_t * pCnf0 = Cnf_Derive( pMan, Aig_ManCoNum(pMan) );
    Cnf_Dat_t * pCnf1 = Cnf_DataDup( pCnf0 );
    Cnf_DataLift( pCnf1, pCnf0->nVars );
    sat_solver * pSat = (sat_solver *)Cnf_DataWriteIntoSolver( pCnf0, 1, 0 );
    Cnf_DataWriteIntoSolverInt( pSat, pCnf1, 1, 0 );

    // add equivalence clauses
    int enableStart = pSat->size;
    sat_solver_setnvars( pSat, enableStart + PiNum );
    Abc_NtkForEachPi( pNtkCone, pPi, j ) {
      int PiID = Aig_ObjId( (Aig_Obj_t *)pPi->pCopy );
      int PiVar0 = pCnf0->pVarNums[ PiID ];
      int PiVar1 = pCnf1->pVarNums[ PiID ];
      int enableVar = enableStart + j;
      sat_solver_add_buffer_enable( pSat, PiVar0, PiVar1, enableVar, 0 );
    }

    // set assumptions
    int assumpNum = PiNum + 4;
    int Pi0 = PiNum  , Pi1 = PiNum+1;
    int Po0 = PiNum+2, Po1 = PiNum+3;
    lit assump[assumpNum];
    // enable all equivalence clauses
    for (j = 0; j < PiNum; ++j)
      assump[j] = toLitCond( enableStart + j, 0 );


    Abc_Obj_t * pConePo = Abc_NtkPo( pNtkCone, 0 );
    int PoID = Aig_ObjId( (Aig_Obj_t *)Abc_ObjFanin0(pConePo)->pCopy );
    Abc_NtkForEachPi( pNtkCone, pPi, j ) {
      // if Pi is not in cone
      if ( !Abc_NodeIsTravIdCurrent( pPi ) ) {
        Vec_PtrPush( posUnateVec, pPi );
        Vec_PtrPush( negUnateVec, pPi );
        continue;
      }

      assump[j] = lit_neg( assump[j] );
      int PiID = Aig_ObjId( (Aig_Obj_t *)pPi->pCopy );
      bool isBinate = true;

      // assign Pi0 = 0, Pi1 = 1
      assump[Pi0] = toLitCond( pCnf0->pVarNums[ PiID ], 1 );
      assump[Pi1] = toLitCond( pCnf1->pVarNums[ PiID ], 0 );

      // check negative unate: assign Po0 = 0, Po1 = 1
      assump[Po0] = toLitCond( pCnf0->pVarNums[ PoID ], 1 );
      assump[Po1] = toLitCond( pCnf1->pVarNums[ PoID ], 0 );
      if (sat_solver_simplify( pSat ) == l_False ||
          sat_solver_solve( pSat, assump, assump + assumpNum, 0, 0, 0, 0 ) == l_False) {
        isBinate = false;
        Vec_PtrPush( negUnateVec, pPi );
      }

      // check positive unate: assign Po0 = 1, Po1 = 0
      assump[Po0] = lit_neg( assump[Po0] );
      assump[Po1] = lit_neg( assump[Po1] );
      if (sat_solver_simplify( pSat ) == l_False ||
          sat_solver_solve( pSat, assump, assump + assumpNum, 0, 0, 0, 0 ) == l_False) {
        isBinate = false;
        Vec_PtrPush( posUnateVec, pPi );
      }

      if (isBinate) Vec_PtrPush( binateVec, pPi );
 
      assump[j] = lit_neg( assump[j] );
    }

    // if Po is complemented, swap +unate and -unate
    if ( Abc_ObjFaninC0( pPo ) ) {
      Vec_Ptr_t * tmp = posUnateVec;
      posUnateVec = negUnateVec;
      negUnateVec = tmp;
    }

    Vec_PtrSort( posUnateVec, (int (*)()) Lsv_sortCompare );
    Vec_PtrSort( negUnateVec, (int (*)()) Lsv_sortCompare );
    Vec_PtrSort( binateVec, (int (*)()) Lsv_sortCompare );

    printf("node %s:\n", Abc_ObjName(pPo));
    Lsv_printInputs( "+unate inputs", posUnateVec );
    Lsv_printInputs( "-unate inputs", negUnateVec );
    Lsv_printInputs( "binate inputs", binateVec );

    Vec_PtrClear( posUnateVec );
    Vec_PtrClear( negUnateVec );
    Vec_PtrClear( binateVec );

    Aig_ManStop( pMan );
    Cnf_DataFree( pCnf0 );
    Cnf_DataFree( pCnf1 );
    sat_solver_delete( pSat );
    Abc_NtkDelete( pNtkCone );
  }

  Vec_PtrFree( posUnateVec );
  Vec_PtrFree( negUnateVec );
  Vec_PtrFree( binateVec );
}

int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
  Abc_Print(-2, "\t        prints the unate information for each primary output in terms of all primary inputs\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
