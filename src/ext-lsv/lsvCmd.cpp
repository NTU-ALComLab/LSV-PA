// src/ext-lsv/lsvCmd.cpp
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <map>
#include <set>
#include <vector>
#include <cstdio>

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

  // Expanded form of Abc_NtkForEachNode(pNtk, pObj, i)
  for (i = 0; (i < Vec_PtrSize((pNtk)->vObjs)) && (((pObj) = Abc_NtkObj(pNtk, i)), 1); i++) 
  {
    if ((pObj) == NULL || !Abc_ObjIsNode(pObj)) {
      // Skip non-node objects
    } else {
      // Print node ID and name
      printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));

      // Iterate over fanins of this node
      Abc_Obj_t* pFanin;
      int j;
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
               Abc_ObjName(pFanin));
      }

      // Print SOP if the network supports it
      if (Abc_NtkHasSop(pNtk)) {
        printf("The SOP of this node:\n%s", (char*)pObj->pData);
      }
    }
  }
}

void Lsv_NtkPrintMoCut(Abc_Ntk_t* pNtk, int k, int l) {
    Abc_Obj_t* pObj;
    int i;

    // Map: Node ID -> set of fanin Node ID
    std::map<int, std::vector<std::set<int>>> nodeCuts;
    // Map: fanin set -> list of node ids
    std::map<std::set<int>, std::set<int>> cutMap;

    Abc_NtkForEachPi(pNtk, pObj, i) {
        int nodeId = Abc_ObjId(pObj);
        nodeCuts[nodeId].push_back({nodeId});
        cutMap[{nodeId}].insert(nodeId);
    }

    Abc_NtkForEachNode(pNtk, pObj, i) {
        int nodeId = Abc_ObjId(pObj);
        Abc_Obj_t* fanin0 = Abc_ObjFanin0(pObj);
        Abc_Obj_t* fanin1 = Abc_ObjFanin1(pObj);
        int FaninId0 = Abc_ObjId(fanin0);
        int FaninId1 = Abc_ObjId(fanin1);

        const auto& cuts0 = nodeCuts[FaninId0];
        const auto& cuts1 = nodeCuts[FaninId1];

        std::vector<std::set<int>> newCuts;

        for (const auto& c0 : cuts0) {
            for (const auto& c1 : cuts1) {
                std::set<int> merged = c0;
                merged.insert(c1.begin(), c1.end());
                if (merged.size() <= k)
                    newCuts.push_back(merged);
            }
        }

        std::set<int> trivial = {FaninId0, FaninId1};
        if (trivial.size() <= k)
            newCuts.push_back(trivial);

        std::set<int> selfCut = {nodeId};
        newCuts.push_back(selfCut);

        std::vector<std::set<int>> irredundant;
        for (auto& c : newCuts) {
            bool redundant = false;
            for (auto& other : irredundant) {
                if (std::includes(c.begin(), c.end(), other.begin(), other.end())) {
                    redundant = true;
                    break;
                }
            }
            if (!redundant) irredundant.push_back(c);
        }

        nodeCuts[nodeId] = irredundant;

        for (const auto& c : irredundant) {
            cutMap[c].insert(nodeId);
        }
    }

    for (const auto& [cutInputs, nodes] : cutMap) {
        if (cutInputs.size() <= k && nodes.size() >= l) {
            bool first = true;
            for (int id : cutInputs) {
                if (!first) printf(" ");
                printf("%d", id);
                first = false;
            }

            printf(" : ");

            first = true;
            for (int id : nodes) {
                if (!first) printf(" ");
                printf("%d", id);
                first = false;
            }

            printf("\n");
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


int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;

  // Parse integers
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);

  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage_cut;
      default:
        goto usage_cut;
    }
  }

  if (argc < 3) {
    Abc_Print(-1, "Error: lsv_printmocut requires two integer arguments <k> <l>.\n");
    goto usage_cut;
  }

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  // Call your function
  Lsv_NtkPrintMoCut(pNtk, k, l);

  return 0;

usage_cut:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
  Abc_Print(-2, "\t        prints the min-cuts with parameters k and l\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
