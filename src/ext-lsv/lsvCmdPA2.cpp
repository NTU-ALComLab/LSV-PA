#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "proof/fra/fra.h"
#include "sat/glucose/AbcGlucose.h"
#include "base/abc/abc.h"
#include "base/main/main.h"
#include <iostream>
#include <string.h>
#include <vector>
#include <unordered_map>
using namespace std;

static int Lsv_CommandPrintpounate(Abc_Frame_t* pAbc, int argc, char** argv);

void initpounate(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintpounate, 0);
}

void destroypounate(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializerpounate = {initpounate, destroypounate};

struct PackageRegistrationManagerpounate {
  PackageRegistrationManagerpounate() { Abc_FrameAddInitializer(&frame_initializerpounate); }
} lsvPackageRegistrationManagerpounate;

// initial ok

struct inputnode{
  //ID = -1, mean doesn't have it
  int initID;
  int coneID;
  char* name;
};

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern "C" Cnf_Dat_t * Cnf_Derive(Aig_Man_t *pAig, int nOutputs);

void Lsv_NtkPrintpounate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* allPi;
  int i;
  int maxPiID=0;
  //get maxPiID
  Abc_NtkForEachPi(pNtk,allPi,i){
    if(Abc_ObjId(allPi)>maxPiID) maxPiID = Abc_ObjId(allPi);
  }
  inputnode Pinode[ maxPiID+1 ];
  unordered_map<string,int> name2initID;
  //init it
  for(i=0;i<maxPiID+1;i++){
    Pinode[i].initID = -1;
  }
  //put name, initID, won't change
  Abc_NtkForEachPi(pNtk,allPi,i){
    Pinode[Abc_ObjId(allPi)].initID = Abc_ObjId(allPi);
    Pinode[Abc_ObjId(allPi)].name = Abc_ObjName(allPi);
    name2initID[Abc_ObjName(allPi)] = Abc_ObjId(allPi);
  }
  //for each PO do it
  Abc_Obj_t* PO;
  Abc_NtkForEachPo(pNtk, PO, i){
    cout<<"node "<<Abc_ObjName(PO)<<":\n";
    // POnode != PO, PO only 1 input: POnode
    Abc_Obj_t* POnode = Abc_NtkFindNode(pNtk,Abc_ObjName(PO));
    // original i use phase function, but other people say this is good, so I use it, not really understand
    // how this function work, but it is correct
    bool isComplment = Abc_ObjFaninC0(PO);
    //but cone id may not be true, it will rerange to 1~n-1, n and only one output
    Abc_Ntk_t* cone = Abc_NtkCreateCone(pNtk,POnode,Abc_ObjName(POnode),0);
    //get Pi number
    int Cinum = Abc_NtkPiNum(cone);
    //init Pinode coneID
    int j;
    for(j=0;j<maxPiID+1;j++){
      Pinode[j].coneID = -1;
    }
    //update coneID
    Abc_Obj_t* PI;
    Abc_NtkForEachPi(cone, PI, j) {
      //cerr<<Abc_ObjName(PI)<<" "<<Abc_ObjId(PI)<<endl;
      //cerr<<name2initID[Abc_ObjName(PI)]<<endl;
      Pinode[ name2initID[Abc_ObjName(PI)] ].coneID = Abc_ObjId(PI);
      //printf("cone Priamy input-%d: name: %s , Id = %d\n", j+1, Abc_ObjName(PI), Abc_ObjId(PI));
      //printf("cone Priamy input-%d: name: %s , Id = %d\n", j+1, Pinode[j+1].name, Abc_ObjId(PI));
    }
    // check unordered map have success do
    // for(j=0;j<maxPiID+1;j++){
    //   if(Pinode[j].initID != -1){
    //     cerr<<j;
    //     cerr<<" initID: "<<Pinode[j].initID;
    //     cerr<<" coneID: "<<Pinode[j].coneID;
    //     cerr<<" name: "<<Pinode[j].name<<endl;
    //   }
    // }
    //change to aig
    Aig_Man_t* coneaig = Abc_NtkToDar(cone,0,0);
    //because only one output, 0 mean CO index
    Aig_Obj_t* coneaig_CO = Aig_ManCo(coneaig,0);
    // I think ID have one to one 
    //debug use
    // Abc_Obj_t* PI;
    // int j;
    // Abc_NtkForEachPi(pNtk, PI, j) {
    //   printf("pNtk Priamy input-%d: name: %s , Id = %d\n", j, Abc_ObjName(PI), Abc_ObjId(PI));
    // }
    // Abc_NtkForEachPi(cone, PI, j) {
    //   printf("Priamy input-%d: name: %s , Id = %d\n", j, Abc_ObjName(PI), Abc_ObjId(PI));
    // }
    // //debug use
    // Aig_Obj_t* Ci;
    // Aig_ManForEachCi(coneaig,Ci,j){
    //   printf("Priamy input-%d: Id = %d\n", j,Aig_ObjId(Ci));
    // } 
    
    //F
    Cnf_Dat_t* cnfconeaig = Cnf_Derive(coneaig,1);
    //copy same F than can use later to F(~x)
    Cnf_Dat_t* negcnfconeaig = Cnf_DataDup(cnfconeaig);
    //move F(~x) node ID to n+1 ~ 2n
    Cnf_DataLift(negcnfconeaig, cnfconeaig->nVars);
    //cout<<cnfconeaig->nVars<<endl;
    //SAT
    sat_solver* pSat = sat_solver_new();
    //need more numCI var to use buffer_enable
    int offset = 2*(cnfconeaig->nVars);
    sat_solver_setnvars(pSat,offset+Aig_ManCiNum(coneaig)+2);
    //add clause
    for(int k=0;k<cnfconeaig->nClauses;k++){
      sat_solver_addclause(pSat,cnfconeaig->pClauses[k],cnfconeaig->pClauses[k+1]);
      sat_solver_addclause(pSat,negcnfconeaig->pClauses[k],negcnfconeaig->pClauses[k+1]);
    }
    //add equivalent buffer
    for(int j=1;j<=Aig_ManCiNum(coneaig);j++){
      sat_solver_add_buffer_enable(pSat,cnfconeaig->pVarNums[j],negcnfconeaig->pVarNums[j],offset+j-1,0);
    }
    //add and for positive F(x) = 0 and F(~x) = 1
    //sat_solver_add_and(pSat,out,in1,in2,cin1,cin2,cout)
    sat_solver_add_and(pSat,offset+Aig_ManCiNum(coneaig),cnfconeaig->pVarNums[coneaig_CO->Id],negcnfconeaig->pVarNums[coneaig_CO->Id],1,0,0);
    //add and for negitive F(x) = 1 and F(~x) = 0
    sat_solver_add_and(pSat,offset+Aig_ManCiNum(coneaig)+1,cnfconeaig->pVarNums[coneaig_CO->Id],negcnfconeaig->pVarNums[coneaig_CO->Id],0,1,0);
    //make assume lit
    //0~2 use to another, 3~N+2 use to enable
    //toLitCond(XXX,0) mean set XXX=1
    lit assume[Cinum+3];
    for(int j=0;j<Aig_ManCiNum(coneaig);j++){
      assume[j+3] = toLitCond(offset + j , 0);
    }
    
    
    // 1:mean is unate
    bool posUnate, negUnate;
    vector<int> posUnate_vec, negUnate_vec, binate_vec;
    // use to check sat status
    int  status;
    for(int indexinit=0; indexinit<=maxPiID; indexinit++){
      if(Pinode[indexinit].initID != -1){
        posUnate = true;
        negUnate = true;
        if(Pinode[indexinit].coneID != -1){
          int index = Pinode[indexinit].coneID;
          // each case set different assume
          // cofactor let cnf->1, negcnf->0
          assume[0] = toLitCond(cnfconeaig->pVarNums[index], 0);
          assume[1] = toLitCond(negcnfconeaig->pVarNums[index], 1);
          // close index enable, (1 mean set to 0)
          assume[index + 2] = toLitCond(offset + index - 1, 1);
          //pos-unate: F(~x)->F(x) so can't (F(~x) and ~F(x)) so set F(~x) = 1 and F(x) = 0
          assume[2] = toLitCond(offset+Aig_ManCiNum(coneaig), 0);
          status = sat_solver_solve(pSat, assume, assume+Cinum+3, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
          posUnate = (status == l_False) ;
          //neg-unate: F(x)->F(~x) so can't (~F(~x) and F(x)) so set F(~x) = 0 and F(x) = 1
          assume[2] = toLitCond(offset+Aig_ManCiNum(coneaig)+1, 0);
          status = sat_solver_solve(pSat, assume, assume+Cinum+3, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
          negUnate = (status == l_False) ;
          //reset enable
          assume[index + 2] = toLitCond(offset + index - 1, 0);
          if(isComplment){
            bool trash = posUnate;
            posUnate = negUnate;
            negUnate = trash;
          }
        }
        if(posUnate || negUnate){
          if(posUnate) posUnate_vec.push_back(indexinit);
          if(negUnate) negUnate_vec.push_back(indexinit);
        }
        else{//mean all false
          binate_vec.push_back(indexinit);
        }
      }
    }
    //then we have posUnate_vec, negUnate_vec, binate_vec to print
    //print
    if(posUnate_vec.size()>0){
      cout<<"+unate inputs: ";
      for(int j=0;j<posUnate_vec.size();j++){
        cout<<Pinode[posUnate_vec[j]].name;
        if(j!=(posUnate_vec.size()-1))cout<<',';
        else cout<<endl;
      }
    }
    if(negUnate_vec.size()>0){
      cout<<"-unate inputs: ";
      for(int j=0;j<negUnate_vec.size();j++){
        cout<<Pinode[negUnate_vec[j]].name;
        if(j!=(negUnate_vec.size()-1))cout<<',';
        else cout<<endl;
      }
    }
    if(binate_vec.size()>0){
      cout<<"binate inputs: ";
      for(int j=0;j<binate_vec.size();j++){
        cout<<Pinode[binate_vec[j]].name;
        if(j!=(binate_vec.size()-1))cout<<',';
        else cout<<endl;
      }
    }
  }
}

int Lsv_CommandPrintpounate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintpounate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_pounateunate [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}