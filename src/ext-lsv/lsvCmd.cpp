#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <set>
#include <map>
#include <string>
#include <algorithm>

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


void Lsv_NtkEnumerateMoCut(Abc_Ntk_t* pNtk, int k, int l) {
  Vec_Ptr_t* vNodes = Abc_NtkDfs(pNtk, 0); 
  Abc_Obj_t* pObj;
  int i;

  // 建一個新的 Vec，先放 PI，再放 DFS nodes
  Vec_Ptr_t* vAll = Vec_PtrAlloc( Abc_NtkCiNum(pNtk) + Vec_PtrSize(vNodes) );

  Abc_NtkForEachCi(pNtk, pObj, i) {
      Vec_PtrPush(vAll, pObj);
  }
  Vec_PtrForEachEntry(Abc_Obj_t*, vNodes, pObj, i) {
      Vec_PtrPush(vAll, pObj);
  }
  // cut set → 支援的 output nodes
  std::map<std::set<int>, std::set<int>> allCuts;
  // node id → 這個 node 的所有 cuts
  std::map<int, std::set<std::set<int>>> nodeCuts;

  Vec_PtrForEachEntry(Abc_Obj_t*, vAll, pObj, i) {
    
      if (Abc_ObjIsCi(pObj)) {
          // primary input 的 cut 只有自己
          //Abc_Print(1, "a");
          std::set<int> baseCut = { Abc_ObjId(pObj) };
          nodeCuts[Abc_ObjId(pObj)].insert(baseCut);
          allCuts[baseCut].insert(Abc_ObjId(pObj));
      } else if (Abc_ObjIsNode(pObj)) {
          //Abc_Print(1, "b");
          Abc_Obj_t* pFanin0 = Abc_ObjFanin(pObj, 0);
          Abc_Obj_t* pFanin1 = Abc_ObjFanin(pObj, 1);
          int id0 = Abc_ObjId(pFanin0);
          int id1 = Abc_ObjId(pFanin1);
          std::set<int> baseCut = { Abc_ObjId(pObj) };
          nodeCuts[Abc_ObjId(pObj)].insert(baseCut);
          allCuts[baseCut].insert(Abc_ObjId(pObj));

          for (auto& cut0 : nodeCuts[id0]) {
              for (auto& cut1 : nodeCuts[id1]) {
                  std::set<int> merged = cut0;
                  merged.insert(cut1.begin(), cut1.end());

                  if ((int)merged.size() <= k) {
                      nodeCuts[Abc_ObjId(pObj)].insert(merged);
      
                  }
              }
          }

          auto& cuts = nodeCuts[Abc_ObjId(pObj)];
          std::set<std::set<int>> toRemove;

          for (auto it1 = cuts.begin(); it1 != cuts.end(); ++it1) {
              for (auto it2 = std::next(it1); it2 != cuts.end(); ++it2) {
                  const auto& a = *it1;
                  const auto& b = *it2;

                  // 如果 a ⊆ b
                  if (std::includes(b.begin(), b.end(), a.begin(), a.end())) {
                      toRemove.insert(b);
                  }
                  // 如果 b ⊆ a
                  else if (std::includes(a.begin(), a.end(), b.begin(), b.end())) {
                      toRemove.insert(a);
                  }
              }
          }

          // 從 cuts 移除 redundant cuts
          for (auto& cut : toRemove) {
              cuts.erase(cut);
          }
          for(auto & cut:cuts){
            allCuts[cut].insert(Abc_ObjId(pObj));
          }

      }
  }

  // 輸出所有 cut
  for (auto& entry : allCuts) {
      const std::set<int>& cutInputs = entry.first;
      const std::set<int>& cutOutputs = entry.second;

      if ((int)cutOutputs.size() >= l) {
          std::string inStr, outStr;

          for (auto it = cutInputs.begin(); it != cutInputs.end(); ++it) {
              if (!inStr.empty()) inStr += " ";
              inStr += std::to_string(*it);
          }

          for (auto it = cutOutputs.begin(); it != cutOutputs.end(); ++it) {
              if (!outStr.empty()) outStr += " ";
              outStr += std::to_string(*it);
          }

          Abc_Print(1, "%s : %s\n", inStr.c_str(), outStr.c_str());
      }
  }

  Vec_PtrFree(vNodes);
  Vec_PtrFree(vAll);
}


int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    assert(Abc_NtkIsStrash(pNtk)); // 確保是 AIG

    if (argc != 3) { // argv[0] = "lsv_printmocut", argv[1] = k, argv[2] = l
        Abc_Print(-1, "Usage: lsv_printmocut <k> <l>\n");
        return 1;
    }

    int k = atoi(argv[1]);
    int l = atoi(argv[2]);

    if (k <= 0 || l <= 0) {
        Abc_Print(-1, "Error: k and l must be positive integers.\n");
        return 1;
    }

    Abc_Print(1, "Enumerating %d-%d multi-output cuts...\n", k, l);

    // 呼叫你的 cut enumeration
    Lsv_NtkEnumerateMoCut(pNtk, k, l);

    return 0;
}
