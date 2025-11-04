#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <unordered_set>
#include <set>
#include <map>
#include <vector>
#include <cstdlib>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "pa1", Lsv_CommandPrintMocut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMocut, 0);
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
      printf("  Fanin-%d: Id = %d, name = %s, type = %d\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin), Abc_ObjType(pFanin));
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

void processNode(Abc_Obj_t* pObj, std::set<int>& visited, std::map<int, std::vector<std::set<int>>>& cutTable, int k) {
  if (Abc_ObjIsPi(pObj)) {
    return;
  }
  Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pObj);
  int fanin0Id = Abc_ObjId(pFanin0);
  if(cutTable.count(fanin0Id) == 0) processNode(pFanin0, visited, cutTable, k);
  Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pObj);
  int fanin1Id = Abc_ObjId(pFanin1);
  if(cutTable.count(fanin1Id) == 0) processNode(pFanin1, visited, cutTable, k);
  int nodeId = Abc_ObjId(pObj);
    for(auto& s0: cutTable[fanin0Id]){
      for(auto& s1: cutTable[fanin1Id]){
        std::set<int> temp;
        // for(auto& e: s0){
        //   temp.insert(e);
        // }
        temp.insert(s0.begin(), s0.end());
        // for(auto& e: s1){
        //   temp.insert(e);
        // }
        temp.insert(s1.begin(), s1.end());
        // printf("\n");
        if(temp.size() <= k){
          cutTable[nodeId].push_back(temp);
        }
      }
    }
    for(auto& s0: cutTable[fanin0Id]){
      std::set<int> temp;
      temp.insert(fanin1Id);
      // for(auto& e: s0){
      //   temp.insert(e);
      // }
      temp.insert(s0.begin(), s0.end());
      // for(auto& e: temp){
      //   printf("%d ", e);
      // }
      // printf("\n");
      if(temp.size() <= k){
        cutTable[nodeId].push_back(temp);
      }
    }
    for(auto& s1: cutTable[fanin1Id]){
      std::set<int> temp;
      temp.insert(fanin0Id);
      // for(auto& e: s1){
      //   temp.insert(e);
      // }
      temp.insert(s1.begin(), s1.end());
      // for(auto& e: temp){
      //   printf("%d ", e);
      // }
      // printf("\n");
      if(temp.size() <= k){
        cutTable[nodeId].push_back(temp);
      }
    }
    if(k >= 2){
      cutTable[nodeId].push_back(std::set<int>{fanin0Id, fanin1Id});
    }
    // printf("node %d has %d cuts\n", nodeId, cutTable[nodeId].size());
    // printf("  fanin-%d: Id = %d, name = %s, type = %d\n", i, Abc_ObjId(pFanin), Abc_ObjName(pFanin), Abc_ObjType(pFanin));
    
}

void Lsv_NtkPrintMocut(Abc_Ntk_t* pNtk, int k, int l) {
  Abc_Obj_t* pObj;
  std::set<int> visited;
  std::map<int, std::vector<std::set<int>>> cutTable;
  int i;
  // printf("Printing MOCUT\n");
  Abc_NtkForEachNode(pNtk, pObj, i) {
    // printf("Object Id = %d, name = %s, type = %d\n", Abc_ObjId(pObj), Abc_ObjName(pObj), Abc_ObjType(pObj));
    if(visited.count(Abc_ObjId(pObj)) == 0){
      visited.insert(Abc_ObjId(pObj));
      processNode(pObj, visited, cutTable, k);
    }
  }
  // for(auto& v: cutTable){
  //   // printf("node %d has %d cuts\n", v.first, v.second.size());
  //   for(auto& s: v.second){
  //     for(auto& e: s){
  //       printf("%d ", e);
  //     }
  //     printf("\n");
  //   }
  //   printf("\n");
  // }
  std::map<std::set<int>, std::set<int>> m;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      int nodeId = Abc_ObjId(pObj);
      for(auto& s: cutTable[nodeId]){
        m[s].insert(nodeId);
      }
    }
    for(auto& v: m){
      if(v.first.size() > k || v.second.size() < l) continue;
      for(auto& e: v.first){
        printf("%d ", e);
      }
      printf(": ");
      for(auto& e: v.second){
        printf("%d ", e);
      }
      printf("\n");
    }
    
}

int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, k = -1, l = -1;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if ( argc != globalUtilOptind + 2 )
        goto usage;
  // try{
    k = atoi(argv[globalUtilOptind]);
    l = atoi(argv[globalUtilOptind + 1]);
  
  if(k < 3 || k > 6) goto usage;
  if(l < 1 || l > 4) goto usage;

  // printf("k = %d, l = %d\n", k, l);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintMocut(pNtk, k, l);
  return 0;


usage:
  Abc_Print(-2, "usage: lsv_print_mocut [-h] <k> <l>\n");
  Abc_Print(-2, "\t        prints k-l multi-output cuts of the network\n");
  Abc_Print(-2, "\t        TODO of the lsv pa1\n");
  Abc_Print(-2, "\t-h    : print the command summary\n");
  Abc_Print(-2, "\tk     : the maximum size of the cut, 3 <= k <= 6 \n");
  Abc_Print(-2, "\tl     : the minimum number of nodes that share the cut, 1 <= l <= 4\n");
  return 1;
}
