/*
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
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
*/

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <algorithm>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

void unateCmdInit(Abc_Frame_t* pAbc){
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSOPUnate, 0);
}

void unateCmdDestroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t unateCmdFrameInitializer = {unateCmdInit, unateCmdDestroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { 
    Abc_FrameAddInitializer(&frame_initializer);
    Abc_FrameAddInitializer(&unateCmdFrameInitializer);
  }
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

bool nodeIDComp(Abc_Obj_t* obj_1, Abc_Obj_t* obj_2){
  return (Abc_ObjId(obj_1) < Abc_ObjId(obj_2));
}

void Lsv_NtkPrintSOPUnate(Abc_Ntk_t* pNtk){
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    
   
    std::vector<Abc_Obj_t*> vPUnate;
    std::vector<Abc_Obj_t*> vNUnate;
    std::vector<Abc_Obj_t*> vBinate;
    std::vector<std::pair<bool,bool> > vCount(Abc_ObjFaninNum(pObj),std::make_pair(0,0));
   // printf("Number of Fanin: %d\n", Abc_ObjFaninNum(pObj));

    int i = 0;
    while(((char*)pObj->pData)[i] != '\0'){
     
      if(i % (Abc_ObjFaninNum(pObj)+3) >= Abc_ObjFaninNum(pObj)) {++i; continue;};
     // printf("%d %c ", i, ((char*)pObj->pData)[i]);
      if(((char*)pObj->pData)[i] == '1') vCount[i % (Abc_ObjFaninNum(pObj)+3)].first = true;
      else if(((char*)pObj->pData)[i] == '0') vCount[i % (Abc_ObjFaninNum(pObj)+3)].second = true;
      ++i;
    }

    Abc_Obj_t* pFanin;
    int j;

    Abc_ObjForEachFanin(pObj, pFanin, j) {
      if(vCount[j].first == true && vCount[j].second == true) vBinate.push_back(pFanin);
      else if(vCount[j].first == true) vPUnate.push_back(pFanin);
      else if(vCount[j].second == true) vNUnate.push_back(pFanin);
    }

    sort(vPUnate.begin(), vPUnate.end(), nodeIDComp);
    sort(vNUnate.begin(), vNUnate.end(), nodeIDComp);
    sort(vBinate.begin(), vBinate.end(), nodeIDComp);

    printf("node %s:\n", Abc_ObjName(pObj));

    if(!vPUnate.empty()){
      printf("+unate inputs:");
      for(int i = 0; i < vPUnate.size(); ++i){
        printf(" %s", Abc_ObjName(vPUnate[i]));
        if(i != vPUnate.size() - 1) printf(",");
      }
      printf("\n");
    }
    if(!vNUnate.empty()){
      printf("-unate inputs:");
      for(int i = 0; i < vNUnate.size(); ++i){
        printf(" %s", Abc_ObjName(vNUnate[i]));
        if(i != vNUnate.size() - 1) printf(",");
      }
      printf("\n");
    }
    if(!vBinate.empty()){
      printf("binate inputs:");
      for(int i = 0; i < vBinate.size(); ++i){
        printf(" %s", Abc_ObjName(vBinate[i]));
        if(i != vBinate.size() - 1) printf(",");
      }
      printf("\n");
    }
  }
}

int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv){
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
  Lsv_NtkPrintSOPUnate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_sopunate [-h]\n");
  Abc_Print(-2, "\t        prints the unate information of each node\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

