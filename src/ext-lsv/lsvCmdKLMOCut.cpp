
#include <algorithm>
#include <iostream>
#include <map>
#include <set>
#include <vector>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

/*
This performs on hashed AIG (strashed network).
It prints out the K-L multi-output cut the network.

A k-feasible cut of a node n is an irredundant cut with no more than k nodes.
In other words, a cut is a k-feasible cut of node n if and only if no subset of this
cut is a cut of node n, and the number of nodes in this cut is not more than k.
A k-l multi-output cut is a k-feasible cut for at least l output nodes.
*/

using namespace std;
namespace {

static int Lsv_Commandmocut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_Commandmocut, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

/* -------------- */

// };
void MergeCut(int node, set<int>& cut0, set<int>& cut1, vector<vector<set<int>>>& Cuts, int k) {
  set<int> newCut = cut0;
  newCut.insert(cut1.begin(), cut1.end());

  if (newCut.size() > k)
    return;
  else {
    // check if newCut is included by any existing cut
    for (auto iter = Cuts[node].begin(); iter != Cuts[node].end();) {
      if (std::includes(newCut.begin(), newCut.end(),
                        iter->begin(), iter->end())) {
        // newCut ⊇ existing cut → discard newCut
        return;
      } else if (std::includes(iter->begin(), iter->end(),
                               newCut.begin(), newCut.end())) {
        // newCut ⊆ existing cut → remove the existing one
        iter = Cuts[node].erase(iter);
      } else {
        ++iter;
      }
    }
    Cuts[node].push_back(newCut);
    return;
  }
};

void FindCut(Abc_Ntk_t* pNtk, int node, vector<vector<set<int>>>& Cuts, int k) {
  if (!Cuts[node].empty())
    return;
  Abc_Obj_t* pObj = Abc_NtkObj(pNtk, node);
  // cout << "node0type " << Abc_ObjType(pObj) << endl;
  // all nodes has cut {node} itself
  Cuts[node].emplace_back(set<int>{node});
  if (Abc_ObjIsPi(pObj)) {
    // cout << "Processing PI node " << node << "...\n";
    return;
  } else if (Abc_ObjIsPo(pObj)) {
    Cuts[node].pop_back();
    // int pFanin0 = Abc_ObjFaninId(pObj, 0);
    // FindCut(pNtk, pFanin0, Cuts, k);
    // Cuts[node].insert(Cuts[node].end(), Cuts[pFanin0].begin(), Cuts[pFanin0].end());
    return;
  } else if (Abc_ObjIsNode(pObj) == 0) {
    Cuts[node].pop_back();
    // cout << "Processing non-PI/PO/non-node node " << node << "...\n";
    return;
  } else {
    // cout << "Processing node " << node << "...\n";
    int n_fanin0 = Abc_ObjFaninId0(pObj);
    int n_fanin1 = Abc_ObjFaninId1(pObj);
    FindCut(pNtk, n_fanin0, Cuts, k);
    FindCut(pNtk, n_fanin1, Cuts, k);
    for (auto& cut0 : Cuts[n_fanin0]) {
      for (auto& cut1 : Cuts[n_fanin1])
        MergeCut(node, cut0, cut1, Cuts, k);
    }
  }
}

void Lsv_NtkMOCut(Abc_Ntk_t* pNtk, int k, int l) {
  // ./abc -c "read lsv/pa1/example.blif; strash; lsv_printmocut 3 1"
  // std::cout << "The K-L multi-output cut of the network:\n";
  // std::cout << "k = " << k << ", l = " << l << "\n";

  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The input network is not a strashed AIG.\n");
    return;
  }

  // Abc_Obj_t* pObj;
  vector<vector<set<int>>> Cuts(Vec_PtrSize((pNtk)->vObjs));  // Cuts[node_id] = { {cut1}, {cut2}, ...}

  for (int i = 0; i < Vec_PtrSize((pNtk)->vObjs); ++i) {
    // cout << "Finding cuts for node " << i << "...\n";
    FindCut(pNtk, i, Cuts, k);
    // cout << "FindCuts " << i << " done\n";
  }
  // cout << "////---//////" << endl;
  // for (int i = 0; i < Vec_PtrSize((pNtk)->vObjs); ++i) {
  //   std::cout << "node " << i << ":\n";
  //   for (auto& cut : Cuts[i]) {
  //     std::cout << "{ ";
  //     for (auto& cutNode : cut)
  //       std::cout << cutNode << ' ';
  //     std::cout << "}\n";
  //   }
  // }
  map<set<int>, set<int>> cutToOutputs;

  for (int i = 0; i < Vec_PtrSize(pNtk->vObjs); ++i) {
    for (auto& cut : Cuts[i]) {
      cutToOutputs[cut].insert(i);
    }
  }
  // std::cout << "The K-L multi-output cuts:\n";
  for (auto& entry : cutToOutputs) {
    const set<int>& cut = entry.first;
    const set<int>& outputs = entry.second;

    if ((int)outputs.size() >= l) {
      // print this multi-output cut
      for (auto leaf : cut) std::cout << leaf << " ";
      cout << ":";
      for (auto out : outputs) std::cout << " " << out;
      cout << "\n";
    }
  }
}

int Lsv_Commandmocut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);  // get current AIG network

  int c;
  int k, l;
  if (argc < 2 || argc > 3) {
    goto usage;
  }

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
  // if (k < 3 || k > 6 || l < 1 || l > 4) {
  //   Abc_Print(-1, "Illegal input parameters.\n");
  //   goto usage;
  // }

  k = (int)atof(argv[1]);
  l = (int)atof(argv[2]);
  Lsv_NtkMOCut(pNtk, k, l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut [-h] <k> <l>\n");
  Abc_Print(-2, "\t        prints the K-L multi-output cut of the network\n");
  Abc_Print(-2, "\t<k>   : k-feasible cut(3 ≤ k ≤ 6)\n");
  Abc_Print(-2, "\t<l>   : l-output nodes(1 ≤ l ≤ 4)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
}  // namespace

/*
vector<vector<vector<int>>> Cuts(Vec_PtrSize(pNtk->vObjs));
map<vector<int>, set<int>> FinalMap; // local, not global

for (int i = 0; i < Vec_PtrSize(pNtk->vObjs); ++i) {
    GetCuts(pNtk, i, Cuts, k);

    for (auto &cut : Cuts[i]) {
        vector<int> key = cut;
        sort(key.begin(), key.end());
        FinalMap[key].insert(i);
    }
}

for (auto &[cut, outputs] : FinalMap) {
    if (outputs.size() >= l) {
        // print cut : outputs
    }
}
*/

// void FindCut(Abc_Ntk_t* pNtk, int node, vector<vector<vector<int>>>& Cuts, int k) {
//   Abc_Obj_t* pObj = Abc_NtkObj(pNtk, node);
//   // all nodes has cut {node} itself
//   Cuts[node].emplace_back(vector<int>{node});
//   if (Abc_ObjIsPi(pObj)) {
//     return;
//   } else if (Abc_ObjIsPo(pObj)) {

//     // int pFanin0 = Abc_ObjFaninId(pObj, 0);
//     // int pFanin1 = Abc_ObjFaninId(pObj, 1);
//     // FindCut(pNtk, pFanin0, Cuts, k);
//     // FindCut(pNtk, pFanin1, Cuts, k);
//     // for (auto& cut0 : Cuts[pFanin0]) {
//     //   for (auto& cut1 : Cuts[pFanin1])
//     //     //MergeTwoCuts(node, cut0, cut1, Cuts, k);
//     // }
//     return;
//   } else {
//     int n_fanin0 = Abc_ObjFaninId0(pObj);
//     int n_fanin1 = Abc_ObjFaninId1(pObj);
//     FindCut(pNtk, n_fanin0, Cuts, k);
//     FindCut(pNtk, n_fanin1, Cuts, k);
//     for (auto& cut0 : Cuts[n_fanin0]) {
//       for (auto& cut1 : Cuts[n_fanin1])
//         MergeCut(node, cut0, cut1, Cuts, k);
//     }
//   }
// }
