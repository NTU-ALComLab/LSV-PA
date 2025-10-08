#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <set>
#include <algorithm>
#include <map>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
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

void Lsv_NtkPrintMocut(Abc_Ntk_t* pNtk, int k, int l) {
  // 1. compute the k-feasible cuts for each node by bottom-up traversal
  Abc_Obj_t* pObj;
  std::map<Abc_Obj_t*, std::vector<std::set<int>>> node_cuts;
  int i;
  
  Abc_NtkForEachObj(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    if (Abc_ObjIsPo(pObj) || Abc_AigNodeIsConst(pObj)) {
      continue;
    }
    node_cuts[pObj].clear();
    // If the node is a Primary Input, continue
    if (Abc_ObjIsPi(pObj)) {
      node_cuts[pObj].push_back(std::set<int>({id}));
      continue;
    }
    // Add the trivial cut {node}
    node_cuts[pObj].push_back(std::set<int>({id}));
    // Cross product of the cuts of its two fanins
    Abc_Obj_t* pFanin0, *pFanin1;
    pFanin0 = Abc_ObjFanin0(pObj);
    pFanin1 = Abc_ObjFanin1(pObj);

    if (!pFanin0 || !pFanin1) {
      continue;
    }

    if (node_cuts.find(pFanin0) == node_cuts.end() || 
        node_cuts.find(pFanin1) == node_cuts.end()) {
      continue;
    }

    const std::vector<std::set<int>>& fanin0_cuts = node_cuts[pFanin0];
    const std::vector<std::set<int>>& fanin1_cuts = node_cuts[pFanin1];

    for (const auto& cut0 : fanin0_cuts) {
      for (const auto& cut1 : fanin1_cuts) {
        std::set<int> new_cut;
        std::set_union(cut0.begin(), cut0.end(), cut1.begin(), cut1.end(),
                       std::inserter(new_cut, new_cut.begin()));
        // Check the size of the new cut
        if ((int)new_cut.size() <= k) {
          node_cuts[pObj].push_back(new_cut);
        }
      }
    }
  }
  // 2. Remove the redundant cuts for each node
  Abc_NtkForEachObj(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    if (Abc_ObjIsPo(pObj) || Abc_AigNodeIsConst(pObj)) {
      continue;
    }
    // Remove redundant cuts
    std::vector<std::set<int>>& cuts = node_cuts[pObj];
    std::vector<std::set<int>> unique_cuts;
    
    for (const auto& cut : cuts) {
      bool is_redundant = false;
      for (const auto& cut_2 : cuts) {
        // Check if cut has no subset cut_2
        if (cut != cut_2 && cut_2.size() < cut.size() && std::includes(cut.begin(), cut.end(), cut_2.begin(), cut_2.end())) {
          is_redundant = true;
          break;
        }
      }
      if (!is_redundant) {
        unique_cuts.push_back(cut);
      }
    }
    cuts = unique_cuts;
  }
  // 3. For each cut, calculate the number of nodes having this cut
  std::map<std::set<int>, std::vector<int>> ml_cut;
  Abc_NtkForEachObj(pNtk, pObj, i) {
    if (node_cuts.find(pObj) != node_cuts.end() && !node_cuts[pObj].empty()) {
      for (const auto& cut : node_cuts[pObj]) {
        ml_cut[cut].push_back(Abc_ObjId(pObj));
      }
    }
  }
  // Print the cuts having number of nodes >= l
  // <in 1> <in 2> ... : <out 1> <out 2> ...
  // nodes in cut : nodes having this cut
  for (auto it = ml_cut.begin(); it != ml_cut.end(); ++it) {
    if ((int)it->second.size() >= l) {
      // sort cut nodes (copy from set to vector and sort)
      std::vector<int> cut_nodes(it->first.begin(), it->first.end());
      std::sort(cut_nodes.begin(), cut_nodes.end());
      // sort output nodes
      std::vector<int> out_nodes = it->second;
      std::sort(out_nodes.begin(), out_nodes.end());

      for (int id : cut_nodes) {
        printf("%d ", id);
      }
      printf(": ");
      for (size_t idx = 0; idx < out_nodes.size(); idx++) {
        int id = out_nodes[idx];
        printf("%d", id);
        if (idx + 1 < out_nodes.size()) printf(" ");
      }
      printf("\n");
    }
  }
}

int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k = 3;
  int l = 2;
  if (argc > 1) k = atoi(argv[1]);
  if (argc > 2) l = atoi(argv[2]);

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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not an AIG. Run 'strash' first.\n");
    return 1;
  }

  Lsv_NtkPrintMocut(pNtk, k, l);

  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut [-h] [<k>] [<l>]\n");
  Abc_Print(-2, "\t        enumerate k-l multi-output cuts in an AIG\n");
  Abc_Print(-2, "\t        default: k=3, l=2\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}