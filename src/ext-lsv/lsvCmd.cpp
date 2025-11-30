#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0); 
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



typedef std::set<int> Cut;
struct CutCompare {
  bool operator()(const Cut& a, const Cut& b) const {
    return std::lexicographical_compare(a.begin(), a.end(), b.begin(), b.end());
  }
};

static void EnumerateCuts(Abc_Obj_t* pObj, int k,
                          std::map<int, std::vector<Cut>>& nodeCuts) {
  int id = Abc_ObjId(pObj);

  if (nodeCuts.find(id) != nodeCuts.end())
    return; 

  std::vector<Cut> cuts;

  if (Abc_ObjIsPi(pObj)) {
    Cut unit;
    unit.insert(id);
    cuts.push_back(unit);
  }
  else if (Abc_ObjIsNode(pObj)) {
    Abc_Obj_t* pFanin0 = Abc_ObjFanin(pObj, 0);
    Abc_Obj_t* pFanin1 = Abc_ObjFanin(pObj, 1);

    EnumerateCuts(pFanin0, k, nodeCuts);
    EnumerateCuts(pFanin1, k, nodeCuts);

    for (auto& cut0 : nodeCuts[Abc_ObjId(pFanin0)]) {
      for (auto& cut1 : nodeCuts[Abc_ObjId(pFanin1)]) {
        Cut merged = cut0;
        merged.insert(cut1.begin(), cut1.end());
        if ((int)merged.size() <= k)
          cuts.push_back(merged);
      }
    }
    Cut unit;
    unit.insert(id);
    cuts.push_back(unit);
  }

  std::sort(cuts.begin(), cuts.end(), CutCompare());
  cuts.erase(std::unique(cuts.begin(), cuts.end(),
                         [](const Cut& a, const Cut& b){ return a == b; }),
             cuts.end());

  nodeCuts[id] = cuts;
}

void Lsv_NtkPrintMoCuts(Abc_Ntk_t* pNtk, int k, int l) {
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return;
  }
  Abc_Obj_t* pObj;
  int i;
  std::map<Cut, std::set<int>, CutCompare> cutToOutputs;
  std::map<int, std::vector<Cut>> nodeCuts;

  Abc_NtkForEachObj(pNtk, pObj, i) {
    if (Abc_ObjIsPi(pObj) || Abc_ObjIsNode(pObj)) {
      EnumerateCuts(pObj, k, nodeCuts);
      int nodeId = Abc_ObjId(pObj);

      for (auto& cut : nodeCuts[nodeId]) {
        cutToOutputs[cut].insert(nodeId);
      }
    }
  }
  for (auto& entry : cutToOutputs) {
    const Cut& cut = entry.first;
    const std::set<int>& outs = entry.second;
    if ((int)outs.size() >= l) {
      bool first = true;
      for (int id : cut) {
        if (!first) printf(" ");
        printf("%d", id);
        first = false;
      }
      printf(" : ");
      first = true;
      for (int id : outs) {
        if (!first) printf(" ");
        printf("%d", id);
        first = false;
      }
      printf("\n");
    }
  }
}


int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {

  int k = atoi(argv[1]);
  int l = atoi(argv[2]);

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintMoCuts(pNtk, k, l);
  return 0;
}
