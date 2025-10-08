#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <set>
#include <map>
#include <algorithm>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintKLCuts(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocuts", Lsv_CommandPrintKLCuts, 0);
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

// Helper function to check if a set is irredundant (no subset is also a cut)
bool Lsv_IsIrredundant(const std::set<int>& cut, Abc_Obj_t* pNode, Abc_Ntk_t* pNtk) {
  // Try removing each element to see if it's still a cut
  for (int elem : cut) {
    std::set<int> subset = cut;
    subset.erase(elem);
    
    // Check if subset is still a cut (using BFS/DFS)
    std::set<int> visited;
    std::vector<int> queue;
    queue.push_back(pNode->Id);
    visited.insert(pNode->Id);
    
    bool isStillCut = true;
    while (!queue.empty() && isStillCut) {
      int current = queue.back();
      queue.pop_back();
      
      if (subset.count(current) > 0) {
        continue; // This is a cut node
      }
      
      Abc_Obj_t* pCurr = Abc_NtkObj(pNtk, current);
      if (Abc_ObjIsPi(pCurr)) {
        if (subset.count(current) == 0) {
          isStillCut = false; // Reached PI not in subset
        }
      } else if (Abc_ObjIsNode(pCurr)) {
        Abc_Obj_t* pFanin;
        int j;
        Abc_ObjForEachFanin(pCurr, pFanin, j) {
          int faninId = Abc_ObjId(pFanin);
          if (visited.find(faninId) == visited.end()) {
            visited.insert(faninId);
            queue.push_back(faninId);
          }
        }
      }
    }
    
    if (isStillCut) {
      return false; // Found a subset that is also a cut
    }
  }
  return true;
}

// Compute k-feasible cuts for a single node
void Lsv_EnumKFeasibleCuts(Abc_Obj_t* pNode, int K, Abc_Ntk_t* pNtk, 
                          std::vector<std::set<int>>& cuts) {
  cuts.clear();
  
  // Trivial cut: the node itself
  if (Abc_ObjIsPi(pNode)) {
    cuts.push_back({pNode->Id});
    return;
  }
  
  // For internal nodes, use BFS to enumerate cuts
  std::set<std::set<int>> allCuts;
  
  // Start with trivial cut
  allCuts.insert({pNode->Id});
  
  // BFS to find all cuts
  std::vector<std::set<int>> frontier;
  frontier.push_back({pNode->Id});
  
  while (!frontier.empty()) {
    std::set<int> current = frontier.back();
    frontier.pop_back();
    
    // Try expanding each node in current cut
    for (int nodeId : current) {
      Abc_Obj_t* pCurr = Abc_NtkObj(pNtk, nodeId);
      
      if (!Abc_ObjIsNode(pCurr)) continue; // Skip PIs
      
      // Create new cut by replacing this node with its fanins
      std::set<int> newCut = current;
      newCut.erase(nodeId);
      
      Abc_Obj_t* pFanin;
      int j;
      Abc_ObjForEachFanin(pCurr, pFanin, j) {
        newCut.insert(Abc_ObjId(pFanin));
      }
      
      // Check if this is a valid k-feasible cut
      if (newCut.size() <= K && allCuts.find(newCut) == allCuts.end()) {
        allCuts.insert(newCut);
        frontier.push_back(newCut);
      }
    }
  }
  
  // Filter to keep only irredundant cuts
  for (const auto& cut : allCuts) {
    if (Lsv_IsIrredundant(cut, pNode, pNtk)) {
      cuts.push_back(cut);
    }
  }
}

void Lsv_PrintKLCuts(Abc_Ntk_t* pNtk, int K, int L) {
  // Map from cut to set of output nodes
  std::map<std::set<int>, std::set<int>> cutToOutputs;
  
  // Compute cuts for each node
  Abc_Obj_t* pObj;
  int i;
  
  // Process all nodes (internal AND nodes and PIs)
  Abc_NtkForEachNode(pNtk, pObj, i) {
    std::vector<std::set<int>> cuts;
    Lsv_EnumKFeasibleCuts(pObj, K, pNtk, cuts);
    
    // Add this node as output for each of its cuts
    for (const auto& cut : cuts) {
      cutToOutputs[cut].insert(Abc_ObjId(pObj));
    }
  }
  
  // Also process primary inputs
  Abc_NtkForEachPi(pNtk, pObj, i) {
    std::vector<std::set<int>> cuts;
    Lsv_EnumKFeasibleCuts(pObj, K, pNtk, cuts);
    
    // Add this node as output for each of its cuts
    for (const auto& cut : cuts) {
      cutToOutputs[cut].insert(Abc_ObjId(pObj));
    }
  }
  
  // Print the cuts that have at least L outputs
  for (const auto& pair : cutToOutputs) {
    if (pair.second.size() >= L) {
      // Print inputs (sorted)
      bool first = true;
      for (int input : pair.first) {
        if (!first) printf(" ");
        printf("%d", input);
        first = false;
      }
      
      printf(" : ");
      
      // Print outputs (sorted)
      first = true;
      for (int output : pair.second) {
        if (!first) printf(" ");
        printf("%d", output);
        first = false;
      }
      
      printf("\n");
    }
  }
}

int Lsv_CommandPrintKLCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int K = 3, L = 1;

  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "k:l:h")) != EOF) {
    switch (c) {
      case 'k':
        K = atoi(globalUtilOptarg);
        if (K < 3 || K > 6) {
          Abc_Print(-1, "K should be between 3 and 6.\n");
          goto usage;
        }
        break;
      case 'l':
        L = atoi(globalUtilOptarg);
        if (L < 1 || L > 4) {
          Abc_Print(-1, "L should be between 1 and 4.\n");
          goto usage;
        }
        break;
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
  
  // Check if network is strashed (AIG)
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not strashed. Please run 'strash' first.\n");
    return 1;
  }
  
  Lsv_PrintKLCuts(pNtk, K, L);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocuts [-k K] [-l L] [-h]\n");
  Abc_Print(-2, "options: \n");
  Abc_Print(-2, "\t-k K\tEnumeration for at most K inputs (Default 3, 3 <= K <= 6)\n");
  Abc_Print(-2, "\t-l L\tEnumeration for at least L outputs (Default 1, 1 <= L <= 4)\n");
  Abc_Print(-2, "\t-h  \tPrint the command usage\n");
  return 1;
}