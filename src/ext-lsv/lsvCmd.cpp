#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <errno.h>
#include <vector>
#include <map>
#include <unordered_map>
#include <set>
#include <algorithm>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCut, 0);
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

typedef std::set<Abc_Obj_t*> CutSet;
typedef std::set<CutSet> SetOfCutSet;

void Lsv_ComputeKFeasibleCut(std::unordered_map<Abc_Obj_t*, SetOfCutSet>& cache, Abc_Obj_t *pNode, int k) {
  SetOfCutSet cutsets;
  CutSet cutset;
  if (Abc_ObjIsPo(pNode)) return;
  if (cache.find(pNode) != cache.end()) return;
  cutset.insert(pNode);
  cutsets.insert(cutset);
  switch (Abc_ObjFaninNum(pNode)) {
    case 0:
      // PI or constant node
      break;
    case 1: {
      Lsv_ComputeKFeasibleCut(cache, Abc_ObjFanin0(pNode), k);
      const SetOfCutSet &cutsets_fanin = cache[Abc_ObjFanin0(pNode)];
      cutsets.insert(cutsets_fanin.begin(), cutsets_fanin.end());
      break;
    }
    case 2: {
      Lsv_ComputeKFeasibleCut(cache, Abc_ObjFanin0(pNode), k);
      Lsv_ComputeKFeasibleCut(cache, Abc_ObjFanin1(pNode), k);
      const SetOfCutSet &cutsets0 = cache[Abc_ObjFanin0(pNode)];
      const SetOfCutSet &cutsets1 = cache[Abc_ObjFanin1(pNode)];
      for (const CutSet &cutset0 : cutsets0) {
        for (const CutSet &cutset1 : cutsets1) {
          CutSet new_cutset = cutset0;
          new_cutset.insert(cutset1.begin(), cutset1.end());
          if (new_cutset.size() > k) continue;
          cutsets.insert(new_cutset);
        }
      }
      break;
    }
  }
  cache[pNode] = cutsets;
}

int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int nArgcNew;
  char** pArgvNew;
  char* endPtr;
  int k;
  int l;
  Abc_Obj_t* pNode;
  int i;
  std::unordered_map<Abc_Obj_t*, SetOfCutSet> cutsets;
  std::map<CutSet, std::vector<Abc_Obj_t*>> cutset_count;

  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  pArgvNew = argv + globalUtilOptind;
  nArgcNew = argc - globalUtilOptind;
  if (nArgcNew != 2) {
    Abc_Print(-1, "Wrong number of arguments.\n");
    return 1;
  }
  k = strtol(pArgvNew[0], &endPtr, 10);
  if (*endPtr != '\0') {
    Abc_Print(-1, "Cannot parse the first argument, k should be a integer but got %s.\n", pArgvNew[0]);
    return 1;
  }
  if (errno == ERANGE) {
    Abc_Print(-1, "The first argument is out of range.\n");
    return 1;
  }
  l = strtol(pArgvNew[1], &endPtr, 10);
  if (*endPtr != '\0') {
    Abc_Print(-1, "Cannot parse the second argument, l should be a integer but got %s.\n", pArgvNew[1]);
    return 1;
  }
  if (errno == ERANGE) {
    Abc_Print(-1, "The second argument is out of range.\n");
    return 1;
  }
  if (k < 3 || k > 6) {
    Abc_Print(-1, "The value of k should be in the range [3, 6].\n");
    return 1;
  }
  if (l < 1 || l > 4) {
    Abc_Print(-1, "The value of l should be in the range [1, 4].\n");
    return 1;
  }

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The command accepts only strashed networks.\n");
    return 1;
  }
  
  Abc_NtkForEachObj(pNtk, pNode, i)
    Lsv_ComputeKFeasibleCut(cutsets, pNode, k);
  for (auto it = cutsets.begin(); it != cutsets.end(); it++) {
    for (const CutSet &cutset : it->second) {
      cutset_count[cutset].push_back(it->first);
    }
  }
  for (auto it = cutset_count.begin(); it != cutset_count.end(); it++) {
    if (it->second.size() < l) continue;
    std::vector<unsigned int> ids;
    for (Abc_Obj_t* obj : it->first)
      ids.push_back(Abc_ObjId(obj));
    std::sort(ids.begin(), ids.end());
    for (unsigned int id : ids)
      Abc_Print(-2, "%d ", id);
    Abc_Print(-2, ": ");
    ids.clear();
    for (Abc_Obj_t* obj : it->second)
      ids.push_back(Abc_ObjId(obj));
    std::sort(ids.begin(), ids.end());
    for (unsigned int id : ids)
      Abc_Print(-2, "%d ", id);
    Abc_Print(-2, "\n");
  }  

  // for (auto it = cutsets.begin(); it != cutsets.end(); it++) {
  //   if (!it->second.size()) continue;
  //   Abc_Print(-2, "Cut set of %d:\n", Abc_ObjId(it->first));
  //   for (const CutSet &cutset : it->second) {
  //     Abc_Print(-2, "> ");
  //     for (Abc_Obj_t* obj : cutset) {
  //       Abc_Print(-2, "%d ", Abc_ObjId(obj));
  //     }
  //     Abc_Print(-2, "\n");
  //   }
  // }

  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut [-h] <k> <l>\n");
  Abc_Print(-2, "\t        prints the multi-output cuts in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  Abc_Print(-2, "\t<k>   : the maximum size of cutset, in the range [3, 6]\n");
  Abc_Print(-2, "\t<l>   : the minimum number of outputs, in the range [1, 4]\n");
  return 1;
}