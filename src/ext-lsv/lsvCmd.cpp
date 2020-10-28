#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <map>
#include <iostream>

using namespace std;

enum unate_type {
  positive = 0,
  negetive,
  unates_size
};

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0);
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

void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  char * temp, *f;
  Abc_NtkForEachNode(pNtk, pObj, i) {

    vector<bool> module_for_bool_vector_size_2(unates_size, false);
    vector<vector<bool> > phases(Abc_ObjFaninNum(pObj), module_for_bool_vector_size_2);

    if (Abc_NtkHasSop(pNtk)) {

      Abc_Obj_t* pFanin;
      int j;
      
      temp = strtok((char*)pObj->pData, " ");
      f = strtok(NULL, "\n");

      while(temp != NULL){
        Abc_ObjForEachFanin(pObj, pFanin, j){
          // don't care
          if (temp[j] == '-'){
            continue;
          }
          // same as f (positive unate probably)     
          else if(temp[j] == *f){
            phases[j][positive] = true;
          }
          // reverse of f (negetive unate probably)
          else{
            phases[j][negetive] = true;
          }
        }  
        temp = strtok(NULL, " ");
        f = strtok(NULL, "\n");    
      }

      map<int, string> binate;
      map<int, string> posunate;
      map<int, string> negunate;
      Abc_ObjForEachFanin(pObj, pFanin, j){
        // binate
        if(phases[j][positive]&&phases[j][negetive]){
          binate[Abc_ObjId(pFanin)] = Abc_ObjName(pFanin);
        }
        // negetive unate
        if(!phases[j][positive]){
          negunate[Abc_ObjId(pFanin)] = Abc_ObjName(pFanin);
        }
        // positive unate
        if(!phases[j][negetive]){
          posunate[Abc_ObjId(pFanin)] = Abc_ObjName(pFanin);
        }
      }

      if(!(binate.empty()&&posunate.empty()&&negunate.empty())){
        printf("node %s:\n", Abc_ObjName(pObj));
      }
      if(!posunate.empty()){
        printf("+unate inputs: ");
        bool flag = false;
        for(auto it : posunate){
          if(flag){
            printf(",%s", it.second.c_str());
          }
          else{
            flag = true;
            printf("%s", it.second.c_str());
          }          
        }
        printf("\n");
      }
      if(!negunate.empty()){
        printf("-unate inputs: ");
        bool flag = false;
        for(auto it : negunate){
          if(flag){
            printf(",%s", it.second.c_str());
          }
          else{
            flag = true;
            printf("%s", it.second.c_str());
          }
        }
        printf("\n");
      }
      if(!binate.empty()){
        printf("binate inputs: ");
        bool flag = false;
        for(auto it : binate){
          if(flag){
            printf(",%s", it.second.c_str());
          }
          else{
            flag = true;
            printf("%s", it.second.c_str());
          }
        }
        printf("\n");
      }
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

int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintSopunate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints the unate information for each node, whose function is expressed in the SOP form\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}