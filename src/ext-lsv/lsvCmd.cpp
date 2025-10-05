#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
// #include <set>

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

void Lsv_NtkPrintmocut(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  std::unordered_map<std::vector<std::set<int>>> LsvCutList; 
  std::set<int> LsvCutTemp;
  Abc_NtkForEachObj(pNtk, pObj, i) {
    if(Abc_ObjIsPi(pObj)){
      LsvCutTemp = {i};
      LsvCutList[i].push_back(LsvCutTemp);
    }else if(Abc_ObjIsNode(pObj)){
      LsvCutTemp = {i};
      LsvCutList[i].push_back(LsvCutTemp);
    }
    // printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    // Abc_Obj_t* pFanin;
    // int pFaninIdList[2];
    // int j;
    // Abc_ObjForEachFanin(pObj, pFanin, j) {
    //   // if(j > 2){
    //   //   break;
    //   // }
    //   printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
    //          Abc_ObjName(pFanin));
    //   pFaninIdList[j] = Abc_ObjId(pFanin);
    // }
    // if (Abc_NtkHasSop(pNtk)) {
    //   printf("The SOP of this node:\n%s", (char*)pObj->pData);
    // }
  }
}

int Lsv_commandPrintmocut(Abc_frame_t* pAbc, int argc, char** argv) {
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
  // main function
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintmocut(pNtk);
  return 0;
  usage:
    Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
    Abc_Print(-2, "\t        prints the nodes in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}
