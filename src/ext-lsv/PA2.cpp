#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <unordered_map>
#include <string>
#include "sat/cnf/cnf.h"
extern "C"{
  Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
  }

void Lsv_NtkPrintNodes_ref(Abc_Ntk_t* pNtk) {
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
      Abc_Obj_t* pFanin;
      int j;
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        printf("  Fanin-%d: Id = %d, name = %s, type = %d\n", j, Abc_ObjId(pFanin),
               Abc_ObjName(pFanin), Abc_ObjType(pFanin));
      }
      if (Abc_NtkHasSop(pNtk)) {
        printf("The SOP of this node:\n%s", (char*)pObj->pData);
      }
    }
}

void unate_bdd(Abc_Ntk_t* pNtk, int k, int i) {
  // Abc_Obj_t* pNode = Abc_NtkObj(pNtk, k);
  // Abc_Obj_t* pFanin;
  // int j;
  // printf("%d",Abc_ObjId(pNode));
  std::unordered_map<std::string, int> m_name2idx;
  DdManager * dd = (DdManager *)pNtk->pManFunc;
  
  Abc_Obj_t* pPi;
  int idx;

  // Iterate through PIs in order
  Abc_NtkForEachPi(pNtk, pPi, idx) {
      // printf("PI %d: Name = %s, Id = %d\n", idx, Abc_ObjName(pPi), Abc_ObjId(pPi));
      m_name2idx[Abc_ObjName(pPi)] = idx;
  }

  Abc_Obj_t* pPo;
  
  // Iterate through POs in order
  Abc_NtkForEachPo(pNtk, pPo, idx) {
      // printf("PO %d: Name = %s, Id = %d\n", idx, Abc_ObjName(pPo), Abc_ObjId(pPo));
  }

  // DdManager * dd = (DdManager *)pNtk->pManFunc;
  pPo = Abc_NtkPo(pNtk, k);
  pPo = Abc_ObjFanin0(pPo);
  DdNode * ddPo = (DdNode *)pPo->pData;
  
  // match the layer of the input i in the BDD by its name
  int layerOfIdiInBdd = -1;
  Vec_Ptr_t * bdd_varsname_arr = Abc_NodeGetFaninNames(pPo);
  void * pName;
  Vec_PtrForEachEntry(char *, bdd_varsname_arr, pName, idx) {
    // printf("BDD var name at layer %d: %s\n", idx, (char*)pName);
    if(strcmp((char*)pName, Abc_ObjName(Abc_NtkPi(pNtk, i))) == 0) {
      layerOfIdiInBdd = idx;
      // break;
    }
  }

  if(layerOfIdiInBdd == -1) {
    printf("independent\n");
    return;
  }

  DdNode * ddPi = Cudd_bddIthVar(dd, layerOfIdiInBdd);
  DdNode * Cof0 = Cudd_Cofactor(dd, ddPo, Cudd_Not(ddPi));
  Cudd_Ref(Cof0);
  DdNode * Cof1 = Cudd_Cofactor(dd, ddPo, ddPi);
  Cudd_Ref(Cof1);
  
  bool posUnate = Cudd_bddLeq(dd, Cof0, Cof1);
  bool negUnate = Cudd_bddLeq(dd, Cof1, Cof0);
  
  if (posUnate) {
      printf("positive unate\n");
      Cudd_RecursiveDeref(dd, Cof0);
      Cudd_RecursiveDeref(dd, Cof1);
      return;
  } else if (negUnate) {
      printf("negative unate\n");
      Cudd_RecursiveDeref(dd, Cof0);
      Cudd_RecursiveDeref(dd, Cof1);
      return;
  } else {
      printf("binate\n");
  }
  
  DdNode * nCof0 = Cudd_Not(Cof0);
  DdNode * nCof1 = Cudd_Not(Cof1);
  DdNode * ddPattern0 = Cudd_bddAnd(dd, Cof0, nCof1);
  DdNode * ddPattern1 = Cudd_bddAnd(dd, Cof1, nCof0);

  DdGen * cex1, * cex0;
  int * cube;
  CUDD_VALUE_TYPE value;
  
  // int numofpi = Abc_NtkPiNum(pNtk);
  cex1 = Cudd_FirstCube(dd, ddPattern1, &cube, &value);
  char * pattern1 = (char*)ABC_ALLOC(char, Abc_NtkPiNum(pNtk) + 1);
  memset(pattern1, '-', Abc_NtkPiNum(pNtk));
  pattern1[Abc_NtkPiNum(pNtk)] = '\0';
  Vec_PtrForEachEntry(char *, bdd_varsname_arr, pName, idx) {
    int tmp = m_name2idx[(char*)pName];
    pattern1[tmp] = cube[idx] == 0 ? '0' : cube[idx] == 1 ? '1' : '-';
  }
  printf("%s\n", pattern1);
    Cudd_GenFree(cex1);

    cex0 = Cudd_FirstCube(dd, ddPattern0, &cube, &value);
    char * pattern0 = (char*)ABC_ALLOC(char, Abc_NtkPiNum(pNtk) + 1);
    memset(pattern0, '-', Abc_NtkPiNum(pNtk));
    pattern0[Abc_NtkPiNum(pNtk)] = '\0';
    Vec_PtrForEachEntry(char *, bdd_varsname_arr, pName, idx) {
      int tmp = m_name2idx[(char*)pName];
      pattern0[tmp] = cube[idx] == 0 ? '0' : cube[idx] == 1 ? '1' : '-';
    }
    printf("%s\n", pattern0);
    Cudd_GenFree(cex0);
    ABC_FREE(pattern1);
    ABC_FREE(pattern0);
}

void unate_sat0(Abc_Ntk_t* pNtk, int k, int i) {
  // printf("unate_sat\n");
  Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
  pPo = Abc_ObjFanin0(pPo);
  char * pNodeName = "test";
  Abc_Ntk_t* pNtkNew;
  pNtkNew = Abc_NtkCreateCone(pNtk, pPo, pNodeName, 1);
  Aig_Man_t * pMan = Abc_NtkToDar(pNtkNew, 0, 1);
  Cnf_Dat_t * pCnf;
  pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
  // Abc_Print( 1, "CNF stats: Vars = %6d. Clauses = %7d. Literals = %8d.   \n", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );
  // Aig_ManPrintStats( pMan );

  // Create two SAT solvers: one for checking cof0 & !cof1, one for !cof0 & cof1
  sat_solver * pSat_posUnateCheck = sat_solver_new();  // checks cof0 & !cof1 (should be UNSAT if pos unate)
  sat_solver * pSat_negUnateCheck = sat_solver_new();  // checks !cof0 & cof1 (should be UNSAT if neg unate)
  
  // Load the first copy of CNF (for cof0)
  Cnf_DataWriteIntoSolverInt( pSat_posUnateCheck, pCnf, 1, 0 );
  Cnf_DataWriteIntoSolverInt( pSat_negUnateCheck, pCnf, 1, 0 );

  int nVarsInOneCnf = pCnf->nVars;
  Cnf_DataLift(pCnf, nVarsInOneCnf);
  
  // Load the second copy of CNF (for cof1)
  Cnf_DataWriteIntoSolverInt( pSat_posUnateCheck, pCnf, 1, 0 );
  Cnf_DataWriteIntoSolverInt( pSat_negUnateCheck, pCnf, 1, 0 );
  
  // Find the i-th PI in the cone network
  Abc_Obj_t* pTargetPi = NULL;
  Abc_Obj_t* pObj;
  int idx;
  Abc_NtkForEachCi(pNtkNew, pObj, idx) {
    const char* piName = Abc_ObjName(pObj);
    const char* origPiName = Abc_ObjName(Abc_NtkPi(pNtk, i));
    if(strcmp(piName, origPiName) == 0) {
      pTargetPi = pObj;
      break;
    }
  }
  
  if(pTargetPi == NULL) {
    printf("PI %d is not in the support of PO %d\n", i, k);
    sat_solver_delete(pSat_posUnateCheck);
    sat_solver_delete(pSat_negUnateCheck);
    Cnf_DataFree(pCnf);
    Aig_ManStop(pMan);
    Abc_NtkDelete(pNtkNew);
    return;
  }
  
  // Add constraints to make all PIs equal in both copies, except the target PI
  Abc_NtkForEachCi(pNtkNew, pObj, idx) {
    int idInCnf_cof0 = pCnf->pVarNums[Abc_ObjId(pObj)] - nVarsInOneCnf;
    int idInCnf_cof1 = pCnf->pVarNums[Abc_ObjId(pObj)];
    
    if(pObj != pTargetPi) {
      // For non-target PIs: make them equal in both copies
      // v_cof0 == v_cof1 is encoded as: (!v_cof0 | v_cof1) & (v_cof0 | !v_cof1)
      lit clause1[2], clause2[2];
      clause1[0] = toLitCond(idInCnf_cof0, 1);  // !v_cof0
      clause1[1] = toLitCond(idInCnf_cof1, 0);  // v_cof1
      clause2[0] = toLitCond(idInCnf_cof0, 0);  // v_cof0
      clause2[1] = toLitCond(idInCnf_cof1, 1);  // !v_cof1
      
      sat_solver_addclause(pSat_posUnateCheck, clause1, clause1 + 2);
      sat_solver_addclause(pSat_posUnateCheck, clause2, clause2 + 2);
      sat_solver_addclause(pSat_negUnateCheck, clause1, clause1 + 2);
      sat_solver_addclause(pSat_negUnateCheck, clause2, clause2 + 2);
    } else {
      // For target PI: set cof0 to 0, cof1 to 1
      lit clause_cof0[1], clause_cof1[1];
      clause_cof0[0] = toLitCond(idInCnf_cof0, 1);  // !v_cof0 (i.e., v_cof0 = 0)
      clause_cof1[0] = toLitCond(idInCnf_cof1, 0);  // v_cof1 (i.e., v_cof1 = 1)
      
      sat_solver_addclause(pSat_posUnateCheck, clause_cof0, clause_cof0 + 1);
      sat_solver_addclause(pSat_posUnateCheck, clause_cof1, clause_cof1 + 1);
      sat_solver_addclause(pSat_negUnateCheck, clause_cof0, clause_cof0 + 1);
      sat_solver_addclause(pSat_negUnateCheck, clause_cof1, clause_cof1 + 1);
    }
  }

  // Get the output variable from the AIG
  Aig_Obj_t* pAigCo = Aig_ManCo(pMan, 0);
  Aig_Obj_t* pAigCoFanin = Aig_ObjFanin0(pAigCo);
  int idInAig = Aig_ObjId(pAigCoFanin);
  int isCompl = Aig_ObjFaninC0(pAigCo);
  
  // Get CNF variable numbers for the output in both copies
  int outVar_cof0 = pCnf->pVarNums[idInAig] - nVarsInOneCnf;
  int outVar_cof1 = pCnf->pVarNums[idInAig];
  
  // For positive unate check: cof0 & !cof1 should be UNSAT
  // Add clauses: out_cof0 = 1 and out_cof1 = 0
  lit clause_out_cof0_pos[1], clause_out_cof1_pos[1];
  clause_out_cof0_pos[0] = toLitCond(outVar_cof0, isCompl);      // out_cof0 = 1
  clause_out_cof1_pos[0] = toLitCond(outVar_cof1, isCompl ^ 1);  // out_cof1 = 0
  sat_solver_addclause(pSat_posUnateCheck, clause_out_cof0_pos, clause_out_cof0_pos + 1);
  sat_solver_addclause(pSat_posUnateCheck, clause_out_cof1_pos, clause_out_cof1_pos + 1);
  
  // For negative unate check: !cof0 & cof1 should be UNSAT
  // Add clauses: out_cof0 = 0 and out_cof1 = 1
  lit clause_out_cof0_neg[1], clause_out_cof1_neg[1];
  clause_out_cof0_neg[0] = toLitCond(outVar_cof0, isCompl ^ 1);  // out_cof0 = 0
  clause_out_cof1_neg[0] = toLitCond(outVar_cof1, isCompl);      // out_cof1 = 1
  sat_solver_addclause(pSat_negUnateCheck, clause_out_cof0_neg, clause_out_cof0_neg + 1);
  sat_solver_addclause(pSat_negUnateCheck, clause_out_cof1_neg, clause_out_cof1_neg + 1);
  
  // Solve both SAT instances
  int isPosUnate = sat_solver_solve(pSat_posUnateCheck, NULL, NULL, 0, 0, 0, 0);
  int isNegUnate = sat_solver_solve(pSat_negUnateCheck, NULL, NULL, 0, 0, 0, 0);
  
  // UNSAT (l_False) means the property holds
  if(isPosUnate == l_False) {
    if(isNegUnate == l_False) {
      printf("independent\n");
      return;
    } else {
      printf("positive_unate\n");
      return;
    }
  } else {
    if(isNegUnate == l_False) {
      printf("negative_unate\n");
      return;
    } else {
      printf("binate\n");
      {
        int * model = pSat_posUnateCheck->model;
        // printf("pattern for positive unate: \n");
        Abc_NtkForEachCi(pNtkNew, pObj, idx) {
          int idInCnf = pCnf->pVarNums[Abc_ObjId(pObj)];
          // int idxInModel = pCnf->pVarNums[idInCnf];
          if(pObj != pTargetPi){
            printf(model[idInCnf] == 1 ? "1" : "0");
            // printf("var[%d] = %d\n", idInCnf, model[idInCnf]);
          }
          else{
            printf("-");
          }
        }
        printf("\n");
      }
      // if(isNegUnate == l_True)
      {
        int * model = pSat_negUnateCheck->model;
        // printf("pattern for negative unate: \n");
        Abc_NtkForEachCi(pNtkNew, pObj, idx) {
          int idInCnf = pCnf->pVarNums[Abc_ObjId(pObj)];
          // int idxInModel = pCnf->pVarNums[idInCnf];
          if(pObj != pTargetPi){
            printf(model[idInCnf] == 1 ? "1" : "0");
          }
          else{
            printf("-");
          }
        }
        printf("\n");
      }
    }
  }
  
  // Cleanup
  sat_solver_delete(pSat_posUnateCheck);
  sat_solver_delete(pSat_negUnateCheck);
  Cnf_DataFree(pCnf);
  Aig_ManStop(pMan);
  Abc_NtkDelete(pNtkNew);
}

void unate_sat(Abc_Ntk_t* pNtk, int k, int i) {
  // printf("unate_sat\n");
  Abc_Obj_t* pPo = Abc_NtkPo(pNtk, k);
  pPo = Abc_ObjFanin0(pPo);
  char * pNodeName = "test";
  Abc_Ntk_t* pNtkNew;
  pNtkNew = Abc_NtkCreateCone(pNtk, pPo, pNodeName, 1);
  Aig_Man_t * pMan = Abc_NtkToDar(pNtkNew, 0, 1);
  Cnf_Dat_t * pCnf;
  pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
  // Abc_Print( 1, "CNF stats: Vars = %6d. Clauses = %7d. Literals = %8d.   \n", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );
  // Aig_ManPrintStats( pMan );

  sat_solver * pSat_posUnateCheck = sat_solver_new(), *pSat_negUnateCheck = sat_solver_new();
  
  Cnf_DataWriteIntoSolverInt( pSat_posUnateCheck, pCnf, 1, 0 );
  Cnf_DataWriteIntoSolverInt( pSat_negUnateCheck, pCnf, 1, 0 );
  // printf("sat_solver_nclauses: %d\n", pSat_temp->size);
  // printf("sat_solver_nclauses: %d\n", sat_solver_nclauses(pSat_temp));

  int nVarsInOneCnf = pCnf->nVars;
  // printf("nVarsInOneCnf: %d\n", nVarsInOneCnf);
  Cnf_DataLift(pCnf, nVarsInOneCnf);
  // the lower is xi=0 and the upper is xi=1
  Cnf_DataWriteIntoSolverInt( pSat_posUnateCheck, pCnf, 1, 0 );
  Cnf_DataWriteIntoSolverInt( pSat_negUnateCheck, pCnf, 1, 0 );
  // printf("sat_solver_nclauses: %d\n", pSat_temp->size);
  // printf("sat_solver_nclauses: %d\n", sat_solver_nclauses(pSat_temp));
  Abc_Obj_t* pObj;
  Abc_Obj_t* pTargetPi = NULL;
  int idx;
  int idInCnf;
  const char* origPiName = Abc_ObjName(Abc_NtkPi(pNtk, i));
  Abc_NtkForEachCi(pNtkNew, pObj, idx) {
    const char* piName = Abc_ObjName(pObj);
    idInCnf = pCnf->pVarNums[Abc_ObjId(pObj)];
    // printf("CI %d: Name = %s, Id = %d\n", idx, Abc_ObjName(pObj), Abc_ObjId(pObj));
    // printf("ID in cnf: %d\n", idInCnf);
    if(strcmp(piName, origPiName) != 0){
      // Non-target PI: make them equal in both copies
      lit var_equal_0[2], var_equal_1[2];
      var_equal_0[0] = toLitCond(idInCnf, 0);
      var_equal_0[1] = toLitCond(idInCnf-nVarsInOneCnf, 1);
      sat_solver_addclause(pSat_posUnateCheck, var_equal_0, var_equal_0 + 2);
      sat_solver_addclause(pSat_negUnateCheck, var_equal_0, var_equal_0 + 2);
      var_equal_1[0] = toLitCond(idInCnf, 1);
      var_equal_1[1] = toLitCond(idInCnf-nVarsInOneCnf, 0); 
      sat_solver_addclause(pSat_posUnateCheck, var_equal_1, var_equal_1 + 2);
      sat_solver_addclause(pSat_negUnateCheck, var_equal_1, var_equal_1 + 2);
    }
    else{
      // Target PI found
      pTargetPi = pObj;
      lit var_cof0[1], var_cof1[1];
      var_cof0[0] = toLitCond(idInCnf - nVarsInOneCnf, 1);
      sat_solver_addclause(pSat_posUnateCheck, var_cof0, var_cof0 + 1);
      sat_solver_addclause(pSat_negUnateCheck, var_cof0, var_cof0 + 1);
      var_cof1[0] = toLitCond(idInCnf, 0);
      sat_solver_addclause(pSat_posUnateCheck, var_cof1, var_cof1 + 1);
      sat_solver_addclause(pSat_negUnateCheck, var_cof1, var_cof1 + 1);
    }
  }

  if(pTargetPi == NULL){
    printf("independent\n");
    sat_solver_delete(pSat_posUnateCheck);
    sat_solver_delete(pSat_negUnateCheck);
    Cnf_DataFree(pCnf);
    Aig_ManStop(pMan);
    Abc_NtkDelete(pNtkNew);
    return;
  }

  // Get the output variable from both copies
  Aig_Obj_t* pAigCo = Aig_ManCo(pMan, 0);
  Aig_Obj_t* pAigCoDriver = Aig_ObjFanin0(pAigCo);
  int idInAig = Aig_ObjId(pAigCoDriver);
  int isCompl = Aig_ObjPhase(pAigCo);
  int outVar = pCnf->pVarNums[idInAig];
  lit po_cof0[1], po_cof1[1];
  // Positive unate check: f(x=1)=1 AND f(x=0)=0 should be UNSAT
  // Upper copy (outVar) is f(x=1), lower copy (outVar - nVarsInOneCnf) is f(x=0)
  po_cof1[0] = toLitCond(outVar, isCompl^1);  // f(x=1) = 1
  sat_solver_addclause(pSat_posUnateCheck, po_cof1, po_cof1 + 1);
  po_cof0[0] = toLitCond(outVar - nVarsInOneCnf, isCompl);  // f(x=0) = 0
  sat_solver_addclause(pSat_posUnateCheck, po_cof0, po_cof0 + 1);
  // Negative unate check: f(x=0)=1 AND f(x=1)=0 should be UNSAT
  po_cof0[0] = toLitCond(outVar - nVarsInOneCnf, isCompl^1);  // f(x=0) = 1
  sat_solver_addclause(pSat_negUnateCheck, po_cof0, po_cof0 + 1);
  po_cof1[0] = toLitCond(outVar, isCompl);  // f(x=1) = 0
  sat_solver_addclause(pSat_negUnateCheck, po_cof1, po_cof1 + 1);
  int isPosUnate = sat_solver_solve(pSat_posUnateCheck, NULL, NULL, 0, 0, 0, 0);
  int isNegUnate = sat_solver_solve(pSat_negUnateCheck, NULL, NULL, 0, 0, 0, 0);
  if(isPosUnate == l_False){
    if(isNegUnate == l_False){
      printf("independent\n");
      return;
    }
    else{
      printf("positive unate\n");
      return;
    }
  }
  else{
    if(isNegUnate == l_False){
      printf("negative unate\n");
      return;
    }
    else{
      printf("binate\n");
    }
  }
  // if(isNegUnate == l_True)
  {
    int * model = pSat_negUnateCheck->model;
    // printf("pattern for negative unate: \n");
    Abc_NtkForEachCi(pNtkNew, pObj, idx) {
      int idInCnf = pCnf->pVarNums[Abc_ObjId(pObj)];
      // int idxInModel = pCnf->pVarNums[idInCnf];
      if(pObj != pTargetPi){
        printf(model[idInCnf] == 1 ? "1" : "0");
      }
      else{
        printf("-");
      }
    }
    printf("\n");
  }
  // if(isPosUnate == l_True)
  {
    int * model = pSat_posUnateCheck->model;
    // printf("pattern for positive unate: \n");
    Abc_NtkForEachCi(pNtkNew, pObj, idx) {
      int idInCnf = pCnf->pVarNums[Abc_ObjId(pObj)];
      // int idxInModel = pCnf->pVarNums[idInCnf];
      if(pObj != pTargetPi){
        printf(model[idInCnf] == 1 ? "1" : "0");
        // printf("var[%d] = %d\n", idInCnf, model[idInCnf]);
      }
      else{
        printf("-");
      }
    }
    printf("\n");
  }
}