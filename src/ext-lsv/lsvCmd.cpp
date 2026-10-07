#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <algorithm>
#include <cstdlib>
#include <map>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
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

// ===================== PA1 4.1: k-feasible cuts =====================

typedef std::vector<int> Cut;  // 一個 cut = 一串排好序的節點 ID

// 合併兩個排好序的 cut（聯集），結果也是排好序、不重複
static Cut Lsv_CutMerge(const Cut& a, const Cut& b) {
  Cut u;
  std::set_union(a.begin(), a.end(), b.begin(), b.end(), std::back_inserter(u));
  return u;
}

// 由下往上算出每個節點的所有 k-feasible cut
static void Lsv_NtkEnumCuts(Abc_Ntk_t* pNtk, int k) {
  std::map<int, std::vector<Cut>> cuts;  // cuts[ID] = 這個節點的所有 cut
  Abc_Obj_t* pObj;
  int i;

  // PI：只有自己
  Abc_NtkForEachPi(pNtk, pObj, i) {
    cuts[Abc_ObjId(pObj)].push_back(Cut{(int)Abc_ObjId(pObj)});
  }

  // AND 節點：ID 由小到大，fanin 一定已經算好
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    int id0 = Abc_ObjId(Abc_ObjFanin0(pObj));
    int id1 = Abc_ObjId(Abc_ObjFanin1(pObj));
    std::vector<Cut>& my = cuts[id];

    my.push_back(Cut{id});  // trivial cut：自己
    for (const Cut& c0 : cuts[id0]) {
      for (const Cut& c1 : cuts[id1]) {
        Cut u = Lsv_CutMerge(c0, c1);
        if ((int)u.size() > k) continue;                            // 太大就丟
        if (std::find(my.begin(), my.end(), u) != my.end()) continue;  // 重複就丟
        my.push_back(u);
      }
    }

    for (const Cut& c : my) {
      printf("%d:", id);
      for (int x : c) printf(" %d", x);
      printf("\n");  // TODO: 之後在這裡補上 ": <truth table>"
    }
  }
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (argc != 2) {
    Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
    return 1;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Please run \"strash\" first.\n");
    return 1;
  }
  Lsv_NtkEnumCuts(pNtk, atoi(argv[1]));
  return 0;
}
