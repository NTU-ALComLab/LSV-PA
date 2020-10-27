#include "lsv.hpp"

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