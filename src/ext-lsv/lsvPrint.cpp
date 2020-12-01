#include "lsv.hpp"

extern "C" {
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

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

void Lsv_NtkPrintPounate(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2){
  extern void * Cnf_DataWriteIntoSolver2( Cnf_Dat_t * p, int nFrames, int fInit );
  extern int    Cnf_DataWriteOrClause2( void * pSat, Cnf_Dat_t * pCnf );
  Abc_Obj_t* pObj, *pPi;
  Abc_Ntk_t* pToggle;
  int i, j;
  int poNum = Abc_NtkPoNum(pNtk1), piNum = Abc_NtkPiNum(pNtk1);
  
  // create f^f'
  Aig_Man_t * pMan1, * pMan2;
  int RetValue;//, clk = Abc_Clock();
  Abc_Obj_t* pBeta = new Abc_Obj_t [poNum];
  Abc_Obj_t* pAlpha = new Abc_Obj_t [piNum];
  assert( Abc_NtkIsStrash(pNtk1) && Abc_NtkIsStrash(pNtk2) );
  assert( Abc_NtkLatchNum(pNtk1) == 0 && Abc_NtkLatchNum(pNtk2) == 0 );
  pMan1 = Abc_NtkToDar( pNtk1, 0, 0 );
  pMan2 = Abc_NtkToDar( pNtk2, 0, 0 );
  cout << "aig : " << pMan1 << " " << pMan2 << endl;

  // derive CNF
  sat_solver2 * pSat;
  Cnf_Dat_t * pCnf;
  Cnf_Dat_t * pCnf2;
  int status;
  abctime clk = Abc_Clock();
  Vec_Int_t * vCiIds;
  assert( Aig_ManRegNum(pMan1) == 0 );
  pMan1->pData = NULL;
  pCnf = Cnf_Derive( pMan1, Aig_ManCoNum(pMan1) );
  pCnf2 = Cnf_Derive( pMan2, Aig_ManCoNum(pMan2) );
  cout << "cnf : " << pCnf << " " << pCnf2 << endl;
  Cnf_DataPrint( pCnf, 1 );

  return;
  pSat = (sat_solver2 *)Cnf_DataWriteIntoSolver2( pCnf, 1, 0 );
  
  int * pBeg, * pEnd;
  int Lits[2], iSatVarOld, iNodeIdOld;
  // derive CNF and express it using new SAT variables
  pCnf2 = Cnf_Derive( pMan2, Aig_ManCoNum(pMan2) );
  // create new variables in the SAT solver
  // sat_solver_setnvars( pSat, sat_solver_nvars(pSat) + pCnf2->nVars );
  // add clauses for this CNF




  // solve each po
  int *pAssumption = new int [piNum+poNum+2]; 
  for(i = 0; i < piNum; ++i){
    pAssumption[i] = toLitCond(pCnf->pVarNums[pAlpha[i].Id], 1);
  }
  for(i = 0; i < poNum; ++i){
    pAssumption[i+piNum] = toLitCond(pCnf->pVarNums[pBeta[i].Id], 0);
  }
  Abc_NtkForEachPo(pNtk1, pObj, i){
    // make assumption
    // po
    pAssumption[i+piNum] = toLitCond(pCnf->pVarNums[pBeta[i].Id], 1);
    if(i != 0)  pAssumption[i-1+piNum] = toLitCond(pCnf->pVarNums[pBeta[i-1].Id], 0);
    // solve
    int j;
    int nVariable = Abc_ObjFaninNum(pObj);
    vector<bool> pPhase(nVariable,0);
    vector<bool> nPhase(nVariable,0);
    string pUnate = "", nUnate = "", binate = "";
    const char* delimiterChar0 = " ", *delimiterChar1 = "\n";
    char *line, *phase;
    Abc_NtkForEachPi(pNtk1, pPi, j){
      // pi
      pAssumption[i] = toLitCond(pCnf->pVarNums[pAlpha[i-1].Id], 1);
      if(i != 0) pAssumption[i-1] = toLitCond(pCnf->pVarNums[pAlpha[i].Id], 0);
      /////////////////////check unate by sat/////////////////////
      // (1,0)
      pAssumption[piNum+poNum] = toLitCond(pCnf->pVarNums[pAlpha[i-1].Id], 1);
      pAssumption[piNum+poNum+1] = toLitCond(pCnf->pVarNums[pAlpha[i-1].Id], 0);
      // (0,1)
    }
    /////////////////////check unate by sat/////////////////////
    
    ///////////////////////////////////////////////////////////
    map<int , string> mNId2string;
    map<int , string> mPId2string;
    map<int , string> mBId2string;
    for(j = 0; j < nVariable; ++j){
      Abc_Obj_t* pFanin;
      pFanin = Abc_ObjFanin(pObj, j);
      if(!pPhase[j]&&!nPhase[j]){
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
