#include "lsv.hpp"
#include "sat/glucose/AbcGlucose.h"



void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int j;
    int nVariable = Abc_ObjFaninNum(pObj);
    vector<bool> pPhase(nVariable,0);
    vector<bool> nPhase(nVariable,0);
    string pUnate = "", nUnate = "", binate = "";
    const char* delimiterChar0 = " ", *delimiterChar1 = "\n";
    char *line, *phase;
    if (Abc_NtkHasSop(pNtk)) {
      // cout << (char*)pObj->pData;
      line = strtok((char*)pObj->pData, delimiterChar0);
      phase = strtok(NULL, delimiterChar1);
      while(line){
        for(j = 0; j < nVariable; ++j){
          char type = *(line+j);
          // cerr << "phase = " << *phase << endl;
          if((type == '1' && ((*phase)=='1')) || (type == '0' && ((*phase)=='0'))){
            pPhase[j] = 1;
            // cerr << j << "is +unate" << endl;
          }
          if((type == '0' && ((*phase)=='1')) || (type == '1' && ((*phase)=='0'))){
            nPhase[j] = 1;
            // cerr << j << "is -unate" << endl;
          }
        }
        line = strtok(NULL, delimiterChar0);
        phase = strtok(NULL, delimiterChar1);
      }
    }
    map<int , string> mNId2string;
    map<int , string> mPId2string;
    map<int , string> mBId2string;
    for(j = 0; j < nVariable; ++j){
      Abc_Obj_t* pFanin;
      pFanin = Abc_ObjFanin(pObj, j);
      if(pPhase[j]&&nPhase[j]){
        mBId2string[Abc_ObjId(pFanin)] = Abc_ObjName(pFanin);
      }
      if(!nPhase[j]){
        mPId2string[Abc_ObjId(pFanin)] = Abc_ObjName(pFanin);
      }
      if(!pPhase[j]){
        mNId2string[Abc_ObjId(pFanin)] = Abc_ObjName(pFanin);
      }
    }
    for(auto& str : mBId2string){
      if(!(binate.size()==0)) binate = binate + "," + str.second;
      else binate = str.second;
    }
    for(auto& str : mPId2string){
      if(!(pUnate.size()==0)) pUnate = pUnate + "," + str.second;
      else pUnate = str.second;
    }
    for(auto& str : mNId2string){
      if(!(nUnate.size()==0)) nUnate = nUnate + "," + str.second;
      else nUnate = str.second;
    }
    if(pUnate.size() || nUnate.size() || binate.size()) printf("node %s:\n", Abc_ObjName(pObj));
    if(pUnate.size()) printf("+unate inputs: %s\n", pUnate.c_str());
    if(nUnate.size()) printf("-unate inputs: %s\n", nUnate.c_str());
    if(binate.size()) printf("binate inputs: %s\n", binate.c_str());
    // getchar();
    // if(Abc_ObjName(pObj) == "new_n510_") getchar(); 

  }
}

void Lsv_NtkPrintPounate(Abc_Ntk_t* pNtk){
  Abc_Obj_t *pNode, *pFanout;
  int i, j;
  
  Network* pNetwork = new Network(pNtk);

  Abc_NtkForEachPo(pNtk, pFanout, i) {
    pNetwork->_coId = i;
    if(!pNetwork->setpNtkCone(pFanout)){
      pNetwork->lsv_printResult();
      continue;
    };
    Aig_Obj_t* pAigObj;
    // record variable information
    // CnfT: Total m variable, CnfF: m+1~2m, newVariable: 2m+1~3m, not: 3m+1
    unordered_map<int, int> mId2var; // T: 1 ouput 2~n input
    Aig_ManForEachCo(pNetwork->_pManT, pAigObj, j) {
      mId2var[Aig_ObjId(Aig_Regular(pAigObj))] = pNetwork->_pCnfT->pVarNums[Aig_ObjId(Aig_Regular(pAigObj))];
    }
    Aig_ManForEachCi(pNetwork->_pManT, pAigObj, j) {
      mId2var[Aig_ObjId(Aig_Regular(pAigObj))] = pNetwork->_pCnfT->pVarNums[Aig_ObjId(Aig_Regular(pAigObj))];
    }
    #ifdef DEBUG
      cerr << "=>>> current node is " << Abc_ObjName(pFanout) << endl;
      cerr << "the current cone has " << Abc_NtkPiNum(pNetwork->_pNtkConeTrue) << "/" << pNetwork->_nCPi << " pis" << endl;
    #endif
    // add clause to sat solver
    #ifdef MINISAT
      sat_solver * pSat;
      pSat = (sat_solver*)pNetwork->lsv_writeCnf2Solver();
    #else
      bmcg_sat_solver * pSat;
      pSat = (bmcg_sat_solver*)pNetwork->lsv_writeCnf2Solver();
    #endif
    
    // solve each pi
    int *pAssumption = new int [pNetwork->_nCPi+2];
    int ret;
    // make assumption (toLitCond 0 -> a 1 -> a')
    for( j = 0; j < pNetwork->_nCPi; ++j ){
      pAssumption[j] = toLitCond(pNetwork->_newVar+j, 1);
    }
    int id;
    Abc_NtkForEachCi(pNetwork->_pNtkConeTrue, pNode, j){
      #ifdef DEBUG
        // getchar();
        cerr << "check pi : " << Abc_ObjName(pNode) << endl;
      #endif
      id = mId2var[Aig_ObjId(Aig_Regular((Aig_Obj_t *)(pNode->pCopy)))];
      // cerr << "ID : " << id << endl;
      pAssumption[id-(pNetwork->_pCnfT->nVars-pNetwork->_nCPi-1)] = lit_neg( pAssumption[id-(pNetwork->_pCnfT->nVars-pNetwork->_nCPi-1)] );
      pAssumption[pNetwork->_nCPi] = toLitCond(id, 1);
      pAssumption[pNetwork->_nCPi+1] = toLitCond(pNetwork->_pCnfT->nVars-1+id, 0);
      #ifdef DEBUG
      cerr << "Assumptions : ";
      for( int k = 0; k < pNetwork->_nCPi + 2; ++k ){
        printf( "%s%d ", pAssumption[k]&1 ? "!":"", pAssumption[k]>>1 );
      }
      cerr << endl;
      #endif
      ret = lsv_solve(pSat, pAssumption, pNetwork->_nCPi+2);
      // positive unate
      if(ret == 1){
        // pNetwork->_pPhase[j] = 1;
        pNetwork->_mName2val[Abc_ObjName(pNode)][0] = 1;
      }
      #ifdef DEBUG
      else{
        cerr << "conterexample : ";
        // int* p = sat_solver_var_value( pSat, conterexample);
        for(int k = 0; k < pNetwork->_nVar; ++k){
          cerr << k << " - " << sat_solver_var_value( pSat, k) << ", " ;
      
        }
        cerr << endl;
      }
      #endif

      pAssumption[pNetwork->_nCPi] = lit_neg( pAssumption[pNetwork->_nCPi] );
      pAssumption[pNetwork->_nCPi+1] = lit_neg( pAssumption[pNetwork->_nCPi+1] );
      ret = lsv_solve(pSat, pAssumption, pNetwork->_nCPi+2);
      #ifdef DEBUG
      cerr << "Assumptions : ";
      for( int k = 0; k < pNetwork->_nCPi + 2; ++k ){
        printf( "%s%d ", pAssumption[k]&1 ? "!":"", pAssumption[k]>>1 );
      }
      cerr << endl;
      #endif
      // negative unate
      if(ret == 1) {
        // pNetwork->_nPhase[j] = 1;
        pNetwork->_mName2val[Abc_ObjName(pNode)][1] = 1;
      }
      #ifdef DEBUG
      else{
        cerr << "conterexample : ";
        // int* p = sat_solver_var_value( pSat, conterexample);
        for(int k = 0; k < pNetwork->_nVar; ++k){
          cerr << k << " - " << sat_solver_var_value( pSat, k) << ", " ;
      
        }
        cerr << endl;
      }
      #endif
      pAssumption[id-(pNetwork->_pCnfT->nVars-pNetwork->_nCPi-1)] = lit_neg( pAssumption[id-(pNetwork->_pCnfT->nVars-pNetwork->_nCPi-1)] );
    }

    // print result
    
    delete [] pAssumption;

    #ifdef MINISAT
      sat_solver_delete( pSat );
    #else
      bmcg_sat_solver_stop(pSat);
    #endif
    pNetwork->lsv_printResult();
  }
  return;
}

#ifdef MINISAT
  void* Network::lsv_writeCnf2Solver(){
    int * pBeg, * pEnd;  
    int i;
    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars( pSat, _nVar);
    
    Cnf_CnfForClause( _pCnfT, pBeg, pEnd, i ) {
      #ifdef DEBUG
        for (int* c = pBeg; c < pEnd; c++ ){
          printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
        }
        printf( "\n" );
      #endif
      if ( !sat_solver_addclause( pSat, pBeg, pEnd ) ){
        sat_solver_delete( pSat );
        cerr << "ERROR" << endl;
        return NULL;
      }
    }
    Cnf_CnfForClause( _pCnfT, pBeg, pEnd, i ) {
      for (int* c = pBeg; c < pEnd; c++ ){
        // cerr << "line 187: before : " << (*c) ;
        (*c) = (*c)&1 ? ((((*c)>>1)+_pCnfT->nVars-1)<<1) + 1 : (((*c)>>1)+_pCnfT->nVars-1)<<1 ;
        // cerr << " after : " << (*c) << endl;
      }
    }
    Cnf_CnfForClause( _pCnfT, pBeg, pEnd, i ) {
      #ifdef DEBUG
        for (int* c = pBeg; c < pEnd; c++ ){
          printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
        }
        printf( "\n" );
      #endif
      if ( !sat_solver_addclause( pSat, pBeg, pEnd ) ){
        sat_solver_delete( pSat );
        cerr << "ERROR" << endl;
        return NULL;
      }
    }
    //add pi
    int pLit[3];
    for( i = 0; i < _nCPi; ++i){
      pLit[0] = toLitCond(_newVar+i, 0);
      pLit[1] = toLitCond(_nVarTPi+i, 0);
      pLit[2] = toLitCond(_nVarFPi+i, 1);
      #ifdef DEBUG
        for (int* c = pLit; c < pLit+3; c++ ){
          printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
        }
        printf( "\n" );
      #endif
      assert(sat_solver_addclause( pSat, pLit, pLit+3 ));
      pLit[1] = lit_neg( pLit[1] );
      pLit[2] = lit_neg( pLit[2] );
      assert(sat_solver_addclause( pSat, pLit, pLit+3 ));
      #ifdef DEBUG
        for (int* c = pLit; c < pLit+3; c++ ){
          printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
        }
        printf( "\n" );
      #endif
    }
    //add not gate
    pLit[0] = toLitCond(_nVar-1, 0);
    // bool flip = Aig_ObjFaninC0((Aig_Obj_t*)_pCurNode->pCopy);
    bool flip = !Aig_ObjFaninC0(Aig_ManCo(_pAig, _coId));
    // cout << "for flip : NamePo :" << Aig_ObjId(Aig_Regular(Aig_ManCo(_pAig, _coId))) << " " << endl;
    // Abc_ObjFaninC0( Abc_NtkFindNode( _pNtk, Abc_ObjName(_pcurPoNode) ));
    if(flip){
      pLit[1] = toLitCond(_pCnfT->nVars, 0);
    }
    else{
      pLit[1] = toLitCond(1, 0);
    }
    assert(sat_solver_addclause( pSat, pLit, pLit+2 ));
    #ifdef DEBUG
      for (int* c = pLit; c < pLit+2; c++ ){
          printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
        }
        printf( "\n" );
    #endif
    pLit[0] = lit_neg( pLit[0] );
    pLit[1] = lit_neg( pLit[1] );
    assert(sat_solver_addclause( pSat, pLit, pLit+2 ));
    #ifdef DEBUG
      for (int* c = pLit; c < pLit+2; c++ ){
          printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
        }
        printf( "\n" );
    #endif
    //add and
    if(flip){
      pLit[0] = toLitCond(1, 0);
      #ifdef DEBUG
        printf( "%s%d \n", (pLit[0])&1 ? "!":"", (pLit[0])>>1 );
      #endif
      assert(sat_solver_addclause( pSat, pLit, pLit+1 ));
    }
    else{
      pLit[0] = toLitCond(_pCnfT->nVars, 0);
      #ifdef DEBUG
        printf( "%s%d \n", (pLit[0])&1 ? "!":"", (pLit[0])>>1 );
      #endif
      assert(sat_solver_addclause( pSat, pLit, pLit+1 ));
    }
    pLit[0] = toLitCond(_nVar-1, 0);
    #ifdef DEBUG
      printf( "%s%d \n", (pLit[0])&1 ? "!":"", (pLit[0])>>1 );
    #endif
    assert(sat_solver_addclause( pSat, pLit, pLit+1 ));
    pLit[0] = toLitCond(_nVar, 0);
    #ifdef DEBUG
      printf( "%s%d \n", (pLit[0])&1 ? "!":"", (pLit[0])>>1 );
    #endif
    assert(sat_solver_addclause( pSat, pLit, pLit+1 ));
    if ( !sat_solver_simplify(pSat) ) {
      sat_solver_delete( pSat );
      cerr << "ERROR" << endl;
      return NULL;
    }
    return (sat_solver*)pSat;
  }
#else 
  void* Network::lsv_writeCnf2Solver(){
    bmcg_sat_solver * pSat;
    int * pBeg, * pEnd;  
    int i;
    pSat = bmcg_sat_solver_start();
    bmcg_sat_solver_set_conflict_budget(pSat, INT_MAX);
    bmcg_sat_solver_set_nvars( pSat, _nVar);
    Cnf_CnfForClause( _pCnfT, pBeg, pEnd, i ) {
      #ifdef DEBUG
        for (int* c = pBeg; c < pEnd; c++ ){
          printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
        }
        printf( "\n" );
      #endif
      assert ( bmcg_sat_solver_addclause( pSat, pBeg, pEnd-pBeg ) );
    }
    Cnf_CnfForClause( _pCnfT, pBeg, pEnd, i ) {
      for (int* c = pBeg; c < pEnd; c++ ){
        // cerr << "line 187: before : " << (*c) ;
        (*c) = (*c)&1 ? ((((*c)>>1)+_pCnfT->nVars-1)<<1) + 1 : (((*c)>>1)+_pCnfT->nVars-1)<<1 ;
        // cerr << " after : " << (*c) << endl;
      }
    }
    Cnf_CnfForClause( _pCnfT, pBeg, pEnd, i ) {
      #ifdef DEBUG
        for (int* c = pBeg; c < pEnd; c++ ){
          printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
        }
        printf( "\n" );
      #endif
      assert ( bmcg_sat_solver_addclause( pSat, pBeg, pEnd-pBeg ) );
    }
    // if ( !sat_solver_simplify(pSat) ) {
    //   sat_solver_delete( pSat );
    //   cerr << "ERROR" << endl;
    //   return NULL;
    // }
    //add pi
    int pLit[3];
    for( i = 0; i < _nCPi; ++i){
      pLit[0] = toLitCond(_newVar+i, 0);
      pLit[1] = toLitCond(_nVarTPi+i, 0);
      pLit[2] = toLitCond(_nVarFPi+i, 1);
      assert(bmcg_sat_solver_addclause( pSat, pLit, 3));
      pLit[1] = lit_neg( pLit[1] );
      pLit[2] = lit_neg( pLit[2] );
      assert(bmcg_sat_solver_addclause( pSat, pLit, 3));
    }
    //add not gate
    pLit[0] = toLitCond(_nVar-1, 0);
    bool flip = !Aig_ObjFaninC0(Aig_ManCo(_pAig, _coId));
    // bool flip = !Aig_ObjFaninC0((Aig_Obj_t*)_pCurNode )->pCopy);
    // Abc_ObjFaninC0( Abc_NtkFindNode( _pNtk, Abc_ObjName(_pcurPoNode) ));
    if(flip){
      pLit[1] = toLitCond(_pCnfT->nVars, 0);
    }
    else{
      pLit[1] = toLitCond(1, 0);
    }
    assert(bmcg_sat_solver_addclause( pSat, pLit, 2));
    #ifdef DEBUG
      for (int* c = pLit; c < pLit+2; c++ ){
          printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
        }
        printf( "\n" );
    #endif
    pLit[0] = lit_neg( pLit[0] );
    pLit[1] = lit_neg( pLit[1] );
    assert(bmcg_sat_solver_addclause( pSat, pLit, 2));
    #ifdef DEBUG
      for (int* c = pLit; c < pLit+2; c++ ){
          printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
        }
        printf( "\n" );
    #endif
    //add and
    if(flip){
      pLit[0] = toLitCond(1, 0);
      if(!bmcg_sat_solver_addclause( pSat, pLit, 1)){
        printf( "%s%d \n", (pLit[0])&1 ? "!":"", (pLit[0])>>1 );
        assert(0);
      }
    }
    else{
      pLit[0] = toLitCond(_pCnfT->nVars, 0);
      if(!bmcg_sat_solver_addclause( pSat, pLit, 1)){
        printf( "%s%d \n", (pLit[0])&1 ? "!":"", (pLit[0])>>1 );
        assert(0);
      }
    }
    pLit[0] = toLitCond(_nVar-1, 0);
    if(!bmcg_sat_solver_addclause( pSat, pLit, 1)){
      printf( "%s%d \n", (pLit[0])&1 ? "!":"", (pLit[0])>>1 );
      assert(0);
    }
    pLit[0] = toLitCond(_nVar, 0);
    if(!bmcg_sat_solver_addclause( pSat, pLit, 1)){
      printf( "%s%d \n", (pLit[0])&1 ? "!":"", (pLit[0])>>1 );
      assert(0);
    }
    return (bmcg_sat_solver*)pSat;
  }
#endif

int Network::setpNtkCone(Abc_Obj_t* pFanout) {
  Abc_Obj_t * pNode;
  _pcurPoNode = pFanout;
  _pCurNode = Abc_NtkFindNode( _pNtk, Abc_ObjName(pFanout) );
  if(Abc_NtkPiNum(Abc_NtkCreateCone( _pNtk, _pCurNode, Abc_ObjName(pFanout), 0 )) == 0){
    vector<bool> val(2,1);
    int i;
    Abc_NtkForEachPi(_pNtk, pNode, i){
      _mName2val[Abc_ObjName(pNode)] = val;
    }
    return false;
  }
  else{
    vector<bool> val(2,0);
    int i;
    Abc_NtkForEachPi(_pNtk, pNode, i){
      _mName2val[Abc_ObjName(pNode)] = val;
    }
  }
  _pNtkConeTrue = Abc_NtkCreateCone( _pNtk, _pCurNode, Abc_ObjName(pFanout), 1 );
  _nCPi = Abc_NtkPiNum(_pNtkConeTrue); 
  _pManT = Abc_NtkToDar( _pNtkConeTrue,  0, 0 );
  _pCnfT = Cnf_Derive( _pManT, Aig_ManCoNum(_pManT) );
  Cnf_DataTranformPolarity( _pCnfT, 0 );
  _newVar = (_pCnfT->nVars << 1) - 1; // +1 -1 -1
  _nVar = (_pCnfT->nVars << 1) + _nCPi; // +1 -1 -1 +1
  _nVarTPi = _pCnfT->nVars - _nCPi - 1; 
  _nVarFPi = ((_pCnfT->nVars-1) << 1) - _nCPi;
  return true;
  // #ifdef DEBUG
  //   Abc_NtkForEachNode(pNtkConeTrue, pObj, j) {
  //     cout << "Name   :" << Abc_ObjName(pObj) << " " << pObj->Id << ", aig : " << ((Aig_Obj_t *)pObj->pCopy)->Id << endl;
  //     // cout << pObj << endl;
  //   }
    // Abc_Obj_t *pObj;
    // Aig_Obj_t *pAigObj;
    // Abc_NtkForEachCo(_pNtk, pObj, i) {
    //   cout << "NameCo :" << Abc_ObjName(pObj) << " " << pObj->Id << endl; //", aig : " << ((Aig_Obj_t *)pObj->pCopy)->Id << endl;
    // }
  //   Abc_NtkForEachCi(pNtkConeTrue, pObj, j) {
  //     cout << "NameCi :" << Abc_ObjName(pObj) << " " << pObj->Id << endl; //", aig : " << ((Aig_Obj_t *)pObj->pCopy)->Id << endl;
  //   }

  //   Aig_ManForEachNode(pManT, pAigObj, j) {
  //     // cout << "Name   :" << Abc_ObjName(pObj) << " " 
  //     cout << Aig_ObjId(Aig_Regular(pAigObj)) << " , cnf ID " << _pCnfT->pVarNums[Aig_ObjId(Aig_Regular(pAigObj))] <<endl;
  //     // cout << pObj << endl;
  //   }
    // Aig_ManForEachCo(_pAig, pAigObj, i) {
    //   // cout << "NamePo :" << Abc_ObjName(pAigObj) << " " << endl; 
    //   cout << "Po : " << Aig_ObjId(Aig_Regular(pAigObj)) << " , cnf ID " << _pCnfT->pVarNums[Aig_ObjId(Aig_Regular(pAigObj))] << endl;

    // }
  //   Aig_ManForEachCi(pManT, pAigObj, j) {
  //   //   cout << "NamePi :" << Abc_ObjName(pObj) << " " 
  //     cout << "Pi : " << Aig_ObjId(Aig_Regular(pAigObj)) << " , cnf ID " << _pCnfT->pVarNums[Aig_ObjId(Aig_Regular(pAigObj))] << endl;
  //   }
  //   int * pBeg1, * pEnd1;
  //   int j;
  //   Cnf_CnfForClause( _pCnfT, pBeg1, pEnd1, j ) {
  //     for (int* c = pBeg1; c < pEnd1; c++ ){
  //       printf( "%s%d ", (*c)&1 ? "!":"", (*c)>>1 );
  //     }
  //     printf( "\n" );
  //   }
  // #endif
};

#ifdef MINISAT
  int lsv_solve(void* pSat, int *lits, int nvar){
    int ret = -1, status;
    status = sat_solver_solve( (sat_solver*)pSat, lits, lits+nvar, (ABC_INT64_T)INT_MAX, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
    if ( status == l_Undef )      ret = -1;
    else if ( status == l_True )  ret = 0;
    else if ( status == l_False ) ret = 1;
    return ret;
  }
#else
  int lsv_solve(void* pSat, int *lits, int nvar){
    int ret = -1, status;
    status = bmcg_sat_solver_solve( (bmcg_sat_solver*)pSat, lits, nvar);
    if ( status == l_Undef )      ret = -1;
    else if ( status == l_True )  ret = 0;
    else if ( status == l_False ) ret = 1;
    return ret;
  }
#endif


void Network::lsv_printResult(){
  string pUnate = "", nUnate = "", binate = "";
  for(auto & id2str : _mId2name){
    _mName2val[id2str.second];
    if(!_mName2val[id2str.second][0] && !_mName2val[id2str.second][1]){
      if(!(binate.size()==0)) binate = binate + "," + id2str.second;
      else binate = id2str.second;
    }
    if(_mName2val[id2str.second][0]){
      if(!(pUnate.size()==0)) pUnate = pUnate + "," + id2str.second;
      else pUnate = id2str.second;
    }
    if(_mName2val[id2str.second][1]){
      if(!(nUnate.size()==0)) nUnate = nUnate + "," + id2str.second;
      else nUnate = id2str.second;
    }
  }
  if(pUnate.size() || nUnate.size() || binate.size()) printf("node %s:\n", Abc_ObjName(_pcurPoNode));
  if(pUnate.size()) printf("+unate inputs: %s\n", pUnate.c_str());
  if(nUnate.size()) printf("-unate inputs: %s\n", nUnate.c_str());
  if(binate.size()) printf("binate inputs: %s\n", binate.c_str());
}