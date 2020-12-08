#include "base/abc/abc.h"
#include "sat/cnf/cnf.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/gia/giaAig.h"
#include "lsvCmd.h"

#include <vector>
#include <string>
#include <iostream>
#include <unordered_map>
using namespace std;

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern "C" Cnf_Dat_t * Cnf_Derive( Aig_Man_t * pAig, int nOutputs );

static int Lsv_CommandPrintSopUnate(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintPoUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopUnate, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPoUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

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

void Lsv_NtkPrintUnate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {

    string pos_unate = "";
    string neg_unate = "";
    string binate = "";
    

    Abc_Obj_t* pFanin;
    int j;
    vector <FanIn> fanins;

    Abc_ObjForEachFanin(pObj, pFanin, j) {
      string s = Abc_ObjName(pFanin);
      fanins.emplace_back(j, Abc_ObjId(pFanin), s);
    }

    
    if (Abc_NtkHasSop(pNtk)) {
      

      string sop = (char*)pObj->pData;

      int col = j + 3;
      int row = sop.size()/col;
      char sop_type = sop[col-2];
      

      for(int ii = 0; ii < col-3; ++ii){
        for(int jj = 0; jj < row; ++jj){
          char cc = sop[jj*col + ii];
          int type = fanins[ii]._type;

          if(type==0){
            if(cc == '1'){
              fanins[ii]._type = 1;
              continue;
            }else if(cc == '0'){
              fanins[ii]._type = 2;
              continue;
            }
          }else if(type==1){
            if(cc == '0'){
              fanins[ii]._type = 3;
              break;
            }
          }else if(type==2){
            if(cc == '1'){
              fanins[ii]._type = 3;
              break;
            }
          }else if(type==3){
            break;
          }
        }
      }

      sort(fanins.begin(), fanins.end());

      for(int ii = 0; ii < fanins.size(); ++ii){
        if(fanins[ii]._type == 0){
          pos_unate = pos_unate + fanins[ii]._name + ",";
          neg_unate = neg_unate + fanins[ii]._name + ",";
        }else if(fanins[ii]._type == 1){
          pos_unate = pos_unate + fanins[ii]._name + ",";
        }else if(fanins[ii]._type == 2){
          neg_unate = neg_unate + fanins[ii]._name + ",";
        }else if(fanins[ii]._type == 3){
          binate = binate + fanins[ii]._name + ",";
        }
      }

      // trim " ,"
      pos_unate = pos_unate.substr(0, pos_unate.length()-1);
      neg_unate = neg_unate.substr(0, neg_unate.length()-1);
      binate = binate.substr(0, binate.length()-1);

      // cout << sop.size() << ", " << col << ", " << row << endl;
      // return;

      if(pos_unate.length() > 0 || neg_unate.length() > 0 || binate.length() > 0 ){
        printf("node %s:\n", Abc_ObjName(pObj));
      }

      if(sop_type=='0'){
        if(neg_unate.length() > 0){
          cout << "+unate inputs: " << neg_unate << endl;
        }
        if(pos_unate.length() > 0){
          cout << "-unate inputs: " << pos_unate << endl;
        }
        if(binate.length() > 0){
          cout << "binate inputs: " << binate << endl;
        }
      }else{
        if(pos_unate.length() > 0){
          cout << "+unate inputs: " << pos_unate << endl;
        }
        if(neg_unate.length() > 0){
          cout << "-unate inputs: " << neg_unate << endl;
        }
        if(binate.length() > 0){
          cout << "binate inputs: " << binate << endl;
        }
      }
      

    }
    
  }

  return;
}

int Lsv_CommandPrintSopUnate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  // Lsv_NtkPrintNodes(pNtk);
  Lsv_NtkPrintUnate(pNtk);
  
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
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


  // implementation starts here

  Abc_Obj_t* pPo;
  int i;
  Abc_NtkForEachPo(pNtk, pPo, i){

    Abc_Ntk_t* pTFINtk = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPo), Abc_ObjName(pPo), 0); // single output network
    if(Abc_ObjFaninC0(pPo)){
      Abc_NtkPo(pTFINtk,0)->fCompl0 ^= 1;
    }
    
    sat_solver * pSat;

    Aig_Man_t * pAig = Abc_NtkToDar(pTFINtk, 0, 0);
    // F
    Cnf_Dat_t * pCnf_F = Cnf_Derive(pAig, Aig_ManCoNum(pAig));
    // F_bar
    Cnf_Dat_t * pCnf_F_bar = Cnf_DataDup(pCnf_F);
    Cnf_DataLift(pCnf_F_bar, pCnf_F->nVars);

    
    // add F into SAT
    pSat = (sat_solver*)Cnf_DataWriteIntoSolver( pCnf_F, 1, 0 );

    
    // add F_bar into SAT
    for (int jj = 0; jj < pCnf_F_bar->nClauses; jj++){
      if ( !sat_solver_addclause( pSat, pCnf_F_bar->pClauses[jj], pCnf_F_bar->pClauses[jj+1] ) )
        {
          sat_solver_delete( pSat );
          continue;
        }
    }

    
    // enabling variables and 
    Abc_Obj_t* pPi_abc;
    int j;

    
    unordered_map <int, int> var2alpha;
    unordered_map <string, int> name2AigId;

    // for each Ci add clause
    Abc_NtkForEachPi(pTFINtk, pPi_abc, j){

      int F_var = pCnf_F->pVarNums[Abc_ObjId(pPi_abc)];
      int F_bar_var = F_var + pCnf_F->nVars;
      int alpha = sat_solver_addvar(pSat);

      var2alpha[F_var] = alpha;
  
      sat_solver_add_buffer_enable(pSat, F_var, F_bar_var, alpha, 0);
      // cerr << Aig_ObjId(pPi) << endl;

      // string s = (string) Abc_ObjName(pPi_abc);
      // name2AigId[s] = Abc_ObjId(pPi_abc);
      
    }



    // for each Ci set assumption and solve for each Ci
    Abc_Obj_t* pPi_other;
    int k;
    int assump_num = Aig_ManCiNum(pAig) + 4;
    int F_out_var = pCnf_F->pVarNums[Aig_ObjId(Aig_ManCo(pAig,0))];  // var number of F out
    int F_bar_out_var = F_out_var + pCnf_F->nVars;  // var number of F_bar out

    string pos_unate = "";
    string neg_unate = "";
    string binate = "";

    Abc_NtkForEachPi(pTFINtk, pPi_abc, j){

      // string s = (string) Abc_ObjName(pPi_abc);
      // if(name2AigId.find(s)==name2AigId.end()){ //don't care inputs
      //   pos_unate = pos_unate + s + ",";
      //   neg_unate = neg_unate + s + ",";
      //   continue;
      // }

      // positive unate
      lit Lits[assump_num];
      Lits[0] = toLitCond(F_out_var, 0);  // F = 1
      Lits[1] = toLitCond(F_bar_out_var, 1); // F~ = 0
      Lits[2] = toLitCond(pCnf_F->pVarNums[Abc_ObjId(pPi_abc)], 1); // F x = 0
      Lits[3] = toLitCond((pCnf_F->pVarNums[Abc_ObjId(pPi_abc)] + pCnf_F->nVars), 0); // F~ x = 1

      int idx = 4;
      Abc_NtkForEachPi(pTFINtk, pPi_other, k){
        int cur_alpha = var2alpha[pCnf_F->pVarNums[Abc_ObjId(pPi_other)]];
        if(Abc_ObjId(pPi_abc) != Abc_ObjId(pPi_other)){ // not cofactor x
          Lits[idx] = toLitCond(cur_alpha, 0);  // alpha
        } else {  //cofactor x 
          Lits[idx] = toLitCond(cur_alpha, 1);  // alpha~
        }
        ++idx;
      }

      int status_pos = sat_solver_solve(pSat, Lits, Lits + assump_num, 0, 0, 0, 0);

      // negative unate
      Lits[2] = toLitCond(pCnf_F->pVarNums[Abc_ObjId(pPi_abc)], 0); // F x = 1
      Lits[3] = toLitCond((pCnf_F->pVarNums[Abc_ObjId(pPi_abc)] + pCnf_F->nVars), 1); // F~ x = 0

      int status_neg = sat_solver_solve(pSat, Lits, Lits + assump_num, 0, 0, 0, 0);

      string s = (string) Abc_ObjName(pPi_abc);
      

      // cerr << status_pos << " " << status_neg << endl;

      if(status_pos==-1 && status_neg==-1){
        name2AigId[s] = 0;
      } else if(status_pos==-1 && status_neg==1){
        name2AigId[s] = 1;
      } else if(status_pos==1 && status_neg==-1){
        name2AigId[s] = 2;
      } else {
        name2AigId[s] = 3;
      }

    }

    Abc_NtkForEachPi(pNtk, pPi_abc, j){
      string s = (string) Abc_ObjName(pPi_abc);
      if(name2AigId.find(s)==name2AigId.end()){ //don't care inputs
        pos_unate = pos_unate + s + ",";
        neg_unate = neg_unate + s + ",";
        continue;
      }

      if(name2AigId[s] == 0){
        pos_unate = pos_unate + s + ",";
        neg_unate = neg_unate + s + ",";
      } else if(name2AigId[s] == 1){
        pos_unate = pos_unate + s + ",";
      } else if(name2AigId[s] == 2){
        neg_unate = neg_unate + s + ",";
      } else if(name2AigId[s] == 3){
        binate = binate + s + ",";
      }
    }


    // trim " ,"
    pos_unate = pos_unate.substr(0, pos_unate.length()-1);
    neg_unate = neg_unate.substr(0, neg_unate.length()-1);
    binate = binate.substr(0, binate.length()-1);

    // output restuls
    cout << "node " << Abc_ObjName(pPo) << ":" << endl;
    if(pos_unate!=""){
      cout << "+unate inputs: " << pos_unate << endl;
    }

    if(neg_unate!=""){
      cout << "-unate inputs: " << neg_unate << endl;
    }

    if(binate!=""){
      cout << "binate inputs: " << binate << endl;
    }
  
  } // end of Abc_NtkForEachPo


  
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_pounates [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}