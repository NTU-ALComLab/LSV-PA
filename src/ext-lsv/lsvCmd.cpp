/****************************************************************************
  FileName     [ lsvCmd.cpp ]
  PackageName  [ print_pounate ]
  Synopsis     [ Define print_pounate commands ]
  Author       [ Qi-Yu Chen (r07943034) ]
  Copyright    [ Copyleft(c) Alcom, GIEE, NTU, Taiwan ]
 ****************************************************************************/
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "sat/cnf/cnf.h"
#include <algorithm>

using namespace std;

static int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPoUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

extern "C" {
  Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}

static int Vec_PtrSortCompare(Abc_Obj_t** pp1, Abc_Obj_t** pp2){
  return Abc_ObjId(*pp1) > Abc_ObjId(*pp2);
}

void PrintUnateInfo(char* str, Vec_Ptr_t* vec){
  if(Vec_PtrSize(vec) == 0)
    return;
  
  Abc_Obj_t* pEntry;
  int i;
  Vec_PtrSort(vec, (int (*)()) Vec_PtrSortCompare);
  
  printf("%s: ", str);
  Vec_PtrForEachEntry(Abc_Obj_t* , vec, pEntry, i){
    printf("%s", Abc_ObjName(pEntry));
    printf("%c", (i == Vec_PtrSize(vec) - 1) ? '\n' : ',');
  }
  Vec_PtrFree(vec);
}

void Lsv_NtkPrintPoUnate(Abc_Ntk_t* pNtk){
  Abc_Obj_t *pObjPo, *pObjPi;
  int i, j;
  int PiNum = Abc_NtkPiNum(pNtk);
  
  // derive unateness for each PO cone
  Abc_NtkForEachPo(pNtk, pObjPo, i){
    Abc_Ntk_t* pNtkCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pObjPo), Abc_ObjName(pObjPo), 1);
    Aig_Man_t* pMan = Abc_NtkToDar(pNtkCone, 0, 0);
    int PoId = Aig_ObjId((Aig_Obj_t* )Abc_ObjFanin0(Abc_NtkPo(pNtkCone, 0))->pCopy);
    
    // derive a CNF formula of an AIG circuit
    Cnf_Dat_t* pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    Cnf_Dat_t* pCnfDup = Cnf_DataDup(pCnf);
    Cnf_DataLift(pCnfDup, pCnf->nVars);
    
    // initialize an SAT solver
    sat_solver* pSat = sat_solver_new();
    Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
    Cnf_DataWriteIntoSolverInt(pSat, pCnfDup, 1, 0);

	int nVars = sat_solver_nvars(pSat);
    sat_solver_setnvars(pSat, nVars+PiNum);
    
	// create assumptions
	int pLits[PiNum+4];
    Abc_NtkForEachPi(pNtkCone, pObjPi, j){
	  pLits[j] = toLitCond(nVars+j, 0);
	  // adds clauses to assert the equivalence
	  int PiId = Aig_ObjId((Aig_Obj_t* )pObjPi->pCopy);
      sat_solver_add_buffer_enable(pSat, pCnf->pVarNums[PiId], pCnfDup->pVarNums[PiId], nVars+j, 0);
    }
    sat_solver_simplify(pSat);

    Vec_Ptr_t* Vec_posUnate = Vec_PtrAlloc(PiNum);
    Vec_Ptr_t* Vec_negUnate = Vec_PtrAlloc(PiNum);
    Vec_Ptr_t* Vec_binate = Vec_PtrAlloc(PiNum);
    
    Abc_NtkForEachPi(pNtkCone, pObjPi, j){
      if (!Abc_NodeIsTravIdCurrent(pObjPi)){
        Vec_PtrPush(Vec_posUnate, pObjPi);
        Vec_PtrPush(Vec_negUnate, pObjPi);
        continue;
      }
      
      int PiId = Aig_ObjId((Aig_Obj_t* )pObjPi->pCopy);
      bool UnateTable[2] = {0};
      pLits[j] = lit_neg(pLits[j]);

      // if the problem is UNSATISFIABLE, the PI is negative unate
      pLits[PiNum] = toLitCond(pCnf->pVarNums[PiId], 0);
      pLits[PiNum+1] = toLitCond(pCnf->pVarNums[PoId], 0);
      pLits[PiNum+2] = toLitCond(pCnfDup->pVarNums[PiId], 1);
      pLits[PiNum+3] = toLitCond(pCnfDup->pVarNums[PoId], 1);
      UnateTable[0] = sat_solver_solve(pSat, pLits, pLits+PiNum+4, 0, 0, 0, 0) == l_False;
      
      // if the problem is UNSATISFIABLE, the PI is positive unate
      pLits[PiNum+1] = lit_neg(pLits[PiNum+1]);
      pLits[PiNum+3] = lit_neg(pLits[PiNum+3]);
      UnateTable[1] = sat_solver_solve(pSat, pLits, pLits+PiNum+4, 0, 0, 0, 0) == l_False;
      
      if(UnateTable[0])
        Vec_PtrPush(Vec_negUnate, pObjPi);
      if(UnateTable[1])
        Vec_PtrPush(Vec_posUnate, pObjPi);
      if(!UnateTable[0] && !UnateTable[1])
        Vec_PtrPush(Vec_binate, pObjPi);
      
      pLits[j] = lit_neg(pLits[j]);
    }
    if (Abc_ObjFaninC0(pObjPo))
      swap(Vec_posUnate, Vec_negUnate);
    
	printf("node %s:\n", Abc_ObjName(pObjPo));
    PrintUnateInfo("+unate inputs", Vec_posUnate);
    PrintUnateInfo("-unate inputs", Vec_negUnate);
    PrintUnateInfo("binate inputs", Vec_binate);

    sat_solver_delete(pSat);
    Cnf_DataFree(pCnf);
    Cnf_DataFree(pCnfDup);
    Aig_ManStop(pMan);
    Abc_NtkDelete(pNtkCone);
  }
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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not a structurally hashed AIG representation.\n");
    return 1;
  }
  Lsv_NtkPrintPoUnate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
  Abc_Print(-2, "\t        prints the unate information for each po\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}