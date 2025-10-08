#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <map>
#include <algorithm>
#include <cstdlib>
#include <cstdio>

static int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCut, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// func
static inline void Normalize(std::vector<int>& v) {
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
}

static inline bool IsSubset(const std::vector<int>& a, const std::vector<int>& b) {
    size_t i = 0, j = 0;
    while (i < a.size() && j < b.size()) {
        if (a[i] == b[j]) { ++i; ++j; }
        else if (a[i] > b[j]) { ++j; }
        else { return false; } // a[i] is not in b
    }
    return i == a.size();
}

static inline void InsertIrredundant(std::vector<std::vector<int>>& bucket,
                                     std::vector<int> cut, int k) {
    Normalize(cut);
    if ((int)cut.size() > k) return;

    // 如果 bucket 中已有 subset ⊆ newCut，則 newCut 是冗餘的，不加入
    for (auto const& oldCut : bucket) {
        if (IsSubset(oldCut, cut)) return;
    }
    // 反過來：移除所有是 newCut 的超集合的舊 cut
    std::vector<std::vector<int>> kept;
    kept.reserve(bucket.size());
    for (auto const& oldCut : bucket) {
        if (!IsSubset(cut, oldCut)) kept.push_back(oldCut);
    }
    kept.push_back(std::move(cut));
    bucket.swap(kept);
}

void Lsv_NtkPrintMOCut(Abc_Ntk_t* pNtk, int k, int l) {
  // Abc_Print(1, "lsv_printmocut called with k = %d, l = %d\n", k, l);
  // TODO: 在這裡實作 multi-output cut enumeration
  // Cuts 存每個 node 的所有 cut
  std::vector<std::vector<std::vector<int>>> Cuts(Abc_NtkObjNumMax(pNtk) + 1);

  Abc_Obj_t* pObj; int i;
  Abc_NtkForEachObj(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      if (Abc_ObjIsPi(pObj)) {
          // PI 的 cut = {自己}
          InsertIrredundant(Cuts[id], std::vector<int>{id}, k);
      }
      else if (Abc_ObjIsNode(pObj)) {
          InsertIrredundant(Cuts[id], std::vector<int>{id}, k);
          // AND node → 由 fanin 的 cut 合併
          Abc_Obj_t* f0 = Abc_ObjFanin0(pObj);
          Abc_Obj_t* f1 = Abc_ObjFanin1(pObj);
          auto& cuts0 = Cuts[Abc_ObjId(f0)];
          auto& cuts1 = Cuts[Abc_ObjId(f1)];

          for (auto& c0 : cuts0) {
              for (auto& c1 : cuts1) {
                  std::vector<int> merged = c0;
                  merged.insert(merged.end(), c1.begin(), c1.end());
                  InsertIrredundant(Cuts[id], std::move(merged), k);
              }
          }
      }
      else {
          // 常數、PO 不用處理
      }
  }
  std::map<std::vector<int>, std::vector<int>> cut2nodes;

  Abc_Obj_t* pObj1;
  int i1;
  Abc_NtkForEachObj(pNtk, pObj1, i1) {
      if (!Abc_ObjIsNode(pObj1)) continue;  // 只考慮 AND nodes
      int id = Abc_ObjId(pObj1);

      for (auto& cut : Cuts[id]) {
          Normalize(cut);
          cut2nodes[cut].push_back(id);
      }
  }

  // 印出結果
  for (auto& kv : cut2nodes) {
      auto& cut = kv.first;
      auto& nodes = kv.second;
      // if (nodes.size() <= 1) continue; // 只有一個 node 不算 group
      if ((int)cut.size() <= k && (int)nodes.size() >= l) {
        // printf("Cut { ");
        for (size_t j=0;j<cut.size();++j) printf("%d ", cut[j]);
        printf(": ");
        for (size_t j=0;j<nodes.size();++j) printf("%d ", nodes[j]);
        printf("\n");
      }
  }
  // // 列印所有 AIG node 的所有 cut（若也想看 PI 的 trivial cut，就把條件改成包含 Abc_ObjIsPi）
  // Abc_Obj_t* pObj2; int i2;
  // Abc_NtkForEachObj(pNtk, pObj2, i2) {
  //     if (!Abc_ObjIsNode(pObj2)) continue;  // 只印 AND nodes；若想包含 PI，改成: if (!(Abc_ObjIsNode(pObj2) || Abc_ObjIsPi(pObj2))) continue;
  //     int id = Abc_ObjId(pObj2);
  //     Abc_Print(1, "Node %d (%s):\n", id, Abc_ObjIsNode(pObj2) ? "AND" : "PI");

  //     auto& myCuts = Cuts[id];
  //     for (size_t t = 0; t < myCuts.size(); ++t) {
  //         const auto& cut = myCuts[t];
  //         printf("  cut %zu: ", t);
  //         for (size_t j = 0; j < cut.size(); ++j) {
  //             printf("%d ", cut[j]);
  //         }
  //         printf("\n");
  //     }
  // }
}

int Lsv_CommandPrintMOCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k = atoi(argv[globalUtilOptind]);
  int l = atoi(argv[globalUtilOptind + 1]);
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

  if (argc - globalUtilOptind != 2) {
    Abc_Print(-1, "Expect two arguments: <k> <l>.\n");
    goto usage;
  }


  if (k < 3 || k > 6 || l < 1 || l > 4) {
    Abc_Print(-1, "Invalid arguments: k must be 3..6, l must be 1..4.\n");
    goto usage;
  }

  Lsv_NtkPrintMOCut(pNtk, k, l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
  Abc_Print(-2, "\t    enumerate k-l multi-output cuts in the network\n");
  Abc_Print(-2, "\t-h : print this command usage\n");
  return 1;
}
// void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
//   Abc_Obj_t* pObj;
//   int i;
//   Abc_NtkForEachNode(pNtk, pObj, i) {
//     printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
//     Abc_Obj_t* pFanin;
//     int j;
//     Abc_ObjForEachFanin(pObj, pFanin, j) {
//       printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
//              Abc_ObjName(pFanin));
//     }
//     if (Abc_NtkHasSop(pNtk)) {
//       printf("The SOP of this node:\n%s", (char*)pObj->pData);
//     }
//   }
// }

// int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
//   Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
//   int c;
//   Extra_UtilGetoptReset();
//   while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
//     switch (c) {
//       case 'h':
//         goto usage;
//       default:
//         goto usage;
//     }
//   }
//   if (!pNtk) {
//     Abc_Print(-1, "Empty network.\n");
//     return 1;
//   }
//   Lsv_NtkPrintNodes(pNtk);
//   return 0;

// usage:
//   Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
//   Abc_Print(-2, "\t        prints the nodes in the network\n");
//   Abc_Print(-2, "\t-h    : print the command usage\n");
//   return 1;
// }