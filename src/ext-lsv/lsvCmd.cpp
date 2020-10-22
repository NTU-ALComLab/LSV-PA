#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "lsvCmd.h"

#include <vector>
#include <string>
#include <iostream>
using namespace std;

static int Lsv_CommandPrintSopUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopUnate, 0);
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

void LSv_NtkPrintUnate(Abc_Ntk_t* pNtk) {
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
      printf("node %s:\n", Abc_ObjName(pObj));

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
          pos_unate = pos_unate + fanins[ii]._name + ", ";
          neg_unate = neg_unate + fanins[ii]._name + ", ";
        }else if(fanins[ii]._type == 1){
          pos_unate = pos_unate + fanins[ii]._name + ", ";
        }else if(fanins[ii]._type == 2){
          neg_unate = neg_unate + fanins[ii]._name + ", ";
        }else if(fanins[ii]._type == 3){
          binate = binate + fanins[ii]._name + ", ";
        }
      }

      // trim " ,"
      pos_unate = pos_unate.substr(0, pos_unate.length()-2);
      neg_unate = neg_unate.substr(0, neg_unate.length()-2);
      binate = binate.substr(0, binate.length()-2);

      // cout << sop.size() << ", " << col << ", " << row << endl;
      // return;

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
  LSv_NtkPrintUnate(pNtk);
  
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}