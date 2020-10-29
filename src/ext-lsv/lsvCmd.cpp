#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_PrintSopunate_Command(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd( pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd( pAbc, "LSV", "lsv_print_sopunate", Lsv_PrintSopunate_Command, 0);
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
      printf("The SOP of this node:\n%s", (char*)pObj->pData); //Abc_ObjData( Abc_Obj_t * pObj )
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

////////My Code////////
bool object_id_compare (Abc_Obj_t* a, Abc_Obj_t* b) { return (Abc_ObjId(a) < Abc_ObjId(b)); }
void print_pos_neg_unate(vector<Abc_Obj_t*> &pos_unate, vector<Abc_Obj_t*> &neg_unate, vector<Abc_Obj_t*> &binate);

int Lsv_PrintSopunate_Command(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pObj;
  Abc_Obj_t* pFanin;
  char * pSop, * pCube;
  int nVars, Value;
  int i, j, k; //i: each node, j: cube for each var, k: each fanin
  int *A;

  vector<Abc_Obj_t*> pos_unate, neg_unate, binate;

  Abc_NtkForEachNode(pNtk, pObj, i) {
    if(Abc_ObjFaninNum(pObj) == 0) continue;

    printf("node %s:\n", Abc_ObjName(pObj));

    if(Abc_NtkHasSop(pNtk)) { 
      pSop = (char*)Abc_ObjData(pObj);
      //printf("The SOP of this node:\n%s", pSop);

      nVars = Abc_SopGetVarNum(pSop);
      //new array
      A = new int[nVars];
      for(int m = 0; m < nVars; m++) //initialization
        A[m] = -1;

      Abc_SopForEachCube( pSop, nVars, pCube ) {
        Abc_CubeForEachVar( pCube, Value, j ) {
          //printf("Value=%d, A[%d]=%d\n", Value, j, A[j]);
          if(A[j] == -1) {
            if(Value == '0' || Value == '1') {
              A[j] = Value - '0';
            }
          }
          else if((A[j]==1 && Value=='0') || (A[j]==0 && Value=='1'))
            A[j] = 3; //binate     
        }
      }

      //catagorize
      Abc_ObjForEachFanin(pObj, pFanin, k) {
        if(A[k] == 1)
          pos_unate.push_back(pFanin);
        else if(A[k] == 0)
          neg_unate.push_back(pFanin);
        else if(A[k] == 3) {
          binate.push_back(pFanin);
          
        }else if(A[k] == -1) {
          pos_unate.push_back(pFanin);
          neg_unate.push_back(pFanin);
        }
      }
      
      delete[] A;

      // sort by object id
      sort(pos_unate.begin(), pos_unate.end(), object_id_compare);
      sort(neg_unate.begin(), neg_unate.end(), object_id_compare);
      sort(binate.begin(), binate.end(), object_id_compare);

      //print
      if(Abc_SopGetPhase(pSop) == 1) 
        print_pos_neg_unate(pos_unate, neg_unate, binate);
      else 
        print_pos_neg_unate(neg_unate, pos_unate, binate); // Abc_SopGetPhase(pSop) == 0 --> negate
    

      pos_unate.clear();
      neg_unate.clear();
      binate.clear();

    }
    
  }
  return 0;
}

void print_pos_neg_unate(vector<Abc_Obj_t*> &pos_unate, vector<Abc_Obj_t*> &neg_unate, vector<Abc_Obj_t*> &binate) {
  if(pos_unate.size() != 0){
    printf("+unate inputs: ");
    for(int m = 0; m < pos_unate.size(); m++) {
      if(m == pos_unate.size() - 1)
        printf("%s\n", Abc_ObjName(pos_unate[m]));
      else  
        printf("%s,", Abc_ObjName(pos_unate[m]));
    }
  }
        
  if(neg_unate.size() != 0){
    printf("-unate inputs: ");
    for(int m = 0; m < neg_unate.size(); m++) {
      if(m == neg_unate.size() - 1)
        printf("%s\n", Abc_ObjName(neg_unate[m]));
      else  
        printf("%s,", Abc_ObjName(neg_unate[m]));
    }
  }

  if(binate.size() != 0){
    printf("binate inputs: ");
    for(int m = 0; m < binate.size(); m++) {
      if(m == binate.size() - 1)
        printf("%s\n", Abc_ObjName(binate[m]));
      else  
        printf("%s,", Abc_ObjName(binate[m]));
    }
  }
}