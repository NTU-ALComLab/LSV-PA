#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <set>
#include <map>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintmocut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintmocut, 0);
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

void enumerate_k_feasible_cuts(Abc_Obj_t* pObj, int k, std::map<int, std::set<std::set<int>>>& nodeIDtoCuts){
  int id = Abc_ObjId(pObj);
  if(nodeIDtoCuts.find(id) != nodeIDtoCuts.end()) {
    return; // already computed
  }
  if(Abc_ObjIsPi(pObj)) {
    nodeIDtoCuts[id].insert({id});
    return;
  }
  Abc_Obj_t* pFanin;
  int j;
  Abc_ObjForEachFanin(pObj, pFanin, j) {
    enumerate_k_feasible_cuts(pFanin, k, nodeIDtoCuts);
  }
  
  nodeIDtoCuts[id].insert({id}); // include trivial cut
  // combine cuts from fanins
  for(auto it1 = nodeIDtoCuts[Abc_ObjId(Abc_ObjFanin0(pObj))].begin(); it1 != nodeIDtoCuts[Abc_ObjId(Abc_ObjFanin0(pObj))].end(); ++it1) {
    for(auto it2 = nodeIDtoCuts[Abc_ObjId(Abc_ObjFanin1(pObj))].begin(); it2 != nodeIDtoCuts[Abc_ObjId(Abc_ObjFanin1(pObj))].end(); ++it2) {
      std::set<int> combinedCut = *it1;
      combinedCut.insert(it2->begin(), it2->end());
      if(combinedCut.size() <= k) {
        nodeIDtoCuts[id].insert(combinedCut);
      }
    }
  }
}

void map_cuts_to_outputs(std::map<int, std::set<std::set<int>>>& nodeIDtoCuts, std::map<std::set<int>, std::set<int>>& cutToOutputs) {
  for(const auto& pair : nodeIDtoCuts) {
    int nodeId = pair.first;
    const std::set<std::set<int>>& cuts = pair.second;
    for(const auto& cut : cuts) {
      cutToOutputs[cut].insert(nodeId);
    }
  }
}

void Lsv_NtkPrintmocut(Abc_Ntk_t* pNtk, int k, int l) {
  std::map<int, std::set<std::set<int>>> nodeIDtoCuts;
  std::map<std::set<int>, std::set<int>> cutToOutputs;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachObj(pNtk, pObj, i) {
    if(Abc_ObjIsNode(pObj)) {
      // call recursive function to enumerate k-feasible cuts and their outputs
      int id = Abc_ObjId(pObj);
      if(nodeIDtoCuts.find(id) == nodeIDtoCuts.end()) {
        enumerate_k_feasible_cuts(pObj, k, nodeIDtoCuts);
      }
    }
  }
  // iterate nodeIDtoCuts to map cuts to outputs
  map_cuts_to_outputs(nodeIDtoCuts, cutToOutputs);
  // iterate through cutToOutputs to find multi-output cuts
  // output format <in_1> <in_2> ... : <out_1> <out_2> ...
  for(const auto& pair : cutToOutputs) {
    const std::set<int>& leafSet = pair.first;
    const std::set<int>& outputs = pair.second;
    if(outputs.size() >= l) {
      for(const int& leaf : leafSet) {
        printf("%d ", leaf);
      }
      printf(": ");
      for(const int& output : outputs) {
        // the final one should not have a trailing space
        if(output == *outputs.rbegin()) {
          printf("%d", output);
          break;
        }
        printf("%d ", output);
      }
      printf("\n");
    }
  }
}

int Lsv_CommandPrintmocut(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (argc != 3) {
    goto usage;
  }
  int k;
  k = atoi(argv[1]);
  int l;
  l = atoi(argv[2]);

  if(!pNtk){
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintmocut(pNtk, k, l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
  Abc_Print(-2, "\t prints the multioutput k-feasible cuts with at least l outputs\n");
  Abc_Print(-2, "\t -h : print the command usage\n");
  return 1;
}