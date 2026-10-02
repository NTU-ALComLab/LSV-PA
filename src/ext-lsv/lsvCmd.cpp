#include <vector>
#include <algorithm>
#include <set>
#include <cstdint>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

using Cut = std::vector<int>;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
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

static Cut MergeCuts(const Cut& c0, const Cut& c1, int k) {
  Cut res;
  res.reserve(c0.size() + c1.size());
  size_t i = 0, j = 0;
  while (i < c0.size() && j < c1.size()) {
    if (c0[i] < c1[j]) {
      res.push_back(c0[i++]);
    } else if (c0[i] > c1[j]) {
      res.push_back(c1[j++]);
    } else {
      res.push_back(c0[i]);
      i++; j++;
    }
    if ((int)res.size() > k) return {};
  }
  while (i < c0.size()) {
    res.push_back(c0[i++]);
    if ((int)res.size() > k) return {};
  }
  while (j < c1.size()) {
    res.push_back(c1[j++]);
    if ((int)res.size() > k) return {};
  }
  return res;
}

static void EnumerateAllCuts(Abc_Ntk_t* pNtk, int k, std::vector<std::vector<Cut>>& allCuts) {
  int maxId = Abc_NtkObjNumMax(pNtk) + 1;
  allCuts.assign(maxId, {});

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachCi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    allCuts[id].push_back({ id });
  }

  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    int id0 = Abc_ObjFaninId0(pObj);
    int id1 = Abc_ObjFaninId1(pObj);
    const auto& cuts0 = allCuts[id0];
    const auto& cuts1 = allCuts[id1];

    std::vector<Cut>& nodeCuts = allCuts[id];
    nodeCuts.push_back({ id }); // trivial cut

    std::set<Cut> seen;
    seen.insert({ id });

    for (const auto& c0 : cuts0) {
      for (const auto& c1 : cuts1) {
        Cut c = MergeCuts(c0, c1, k);
        if (!c.empty() && (int)c.size() <= k) {
          if (seen.insert(c).second) {
            nodeCuts.push_back(c);
          }
        }
      }
    }
  }
}

static void CollectCone_rec(Abc_Obj_t* pNode, const std::vector<int>& cutTag,
                            int travId, std::vector<int>& visited,
                            std::vector<Abc_Obj_t*>& cone) {
  int id = Abc_ObjId(pNode);
  if (cutTag[id] == travId || visited[id] == travId) return;
  visited[id] = travId;
  if (Abc_ObjIsNode(pNode)) {
    CollectCone_rec(Abc_ObjFanin0(pNode), cutTag, travId, visited, cone);
    CollectCone_rec(Abc_ObjFanin1(pNode), cutTag, travId, visited, cone);
    cone.push_back(pNode);
  }
}

static uint64_t ComputeCutTruthTable(Abc_Obj_t* pRoot, const Cut& cut,
                                     int travId,
                                     std::vector<int>& cutTag,
                                     std::vector<int>& visited,
                                     std::vector<uint64_t>& nodeVal,
                                     std::vector<Abc_Obj_t*>& cone) {
  int m = (int)cut.size();
  if (m == 1 && cut[0] == Abc_ObjId(pRoot)) {
    return 2ULL;
  }

  for (int leafId : cut) {
    cutTag[leafId] = travId;
  }

  cone.clear();
  CollectCone_rec(pRoot, cutTag, travId, visited, cone);

  for (int j = 0; j < m; ++j) {
    uint64_t mask = 0;
    for (int p = 0; p < (1 << m); ++p) {
      if ((p >> (m - 1 - j)) & 1) {
        mask |= (1ULL << p);
      }
    }
    nodeVal[cut[j]] = mask;
  }

  for (Abc_Obj_t* pNode : cone) {
    uint64_t v0 = nodeVal[Abc_ObjFaninId0(pNode)];
    if (Abc_ObjFaninC0(pNode)) v0 = ~v0;

    uint64_t v1 = nodeVal[Abc_ObjFaninId1(pNode)];
    if (Abc_ObjFaninC1(pNode)) v1 = ~v1;

    nodeVal[Abc_ObjId(pNode)] = v0 & v1;
  }

  uint64_t tt = nodeVal[Abc_ObjId(pRoot)];
  if (m < 6) {
    tt &= ((1ULL << (1 << m)) - 1ULL);
  }
  return tt;
}

static int ComputeCutBddSize(DdManager* dd, Abc_Obj_t* pRoot, const Cut& cut,
                             int travId,
                             std::vector<int>& cutTag,
                             std::vector<int>& visited,
                             std::vector<DdNode*>& nodeBdd,
                             std::vector<Abc_Obj_t*>& cone) {
  int m = (int)cut.size();
  if (m == 1 && cut[0] == Abc_ObjId(pRoot)) {
    DdNode* bVar = Cudd_bddIthVar(dd, 0);
    return Cudd_DagSize(bVar);
  }

  for (int leafId : cut) {
    cutTag[leafId] = travId;
  }

  cone.clear();
  CollectCone_rec(pRoot, cutTag, travId, visited, cone);

  for (int j = 0; j < m; ++j) {
    nodeBdd[cut[j]] = Cudd_bddIthVar(dd, j);
  }

  for (Abc_Obj_t* pNode : cone) {
    DdNode* bChild0 = nodeBdd[Abc_ObjFaninId0(pNode)];
    if (Abc_ObjFaninC0(pNode)) bChild0 = Cudd_Not(bChild0);

    DdNode* bChild1 = nodeBdd[Abc_ObjFaninId1(pNode)];
    if (Abc_ObjFaninC1(pNode)) bChild1 = Cudd_Not(bChild1);

    DdNode* b = Cudd_bddAnd(dd, bChild0, bChild1);
    Cudd_Ref(b);
    nodeBdd[Abc_ObjId(pNode)] = b;
  }

  DdNode* bRoot = nodeBdd[Abc_ObjId(pRoot)];
  int size = Cudd_DagSize(bRoot);

  for (Abc_Obj_t* pNode : cone) {
    Cudd_RecursiveDeref(dd, nodeBdd[Abc_ObjId(pNode)]);
  }

  return size;
}

static void PrintCut(int nodeId, const Cut& cut) {
  printf("%d:", nodeId);
  for (int leafId : cut) {
    printf(" %d", leafId);
  }
  printf(":");
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG (run 'strash' first).\n");
    return 1;
  }
  if (argc - globalUtilOptind != 1) {
    goto usage;
  }
  {
    int k = atoi(argv[globalUtilOptind]);
    if (k < 2 || k > 6) {
      Abc_Print(-1, "k must be between 2 and 6.\n");
      return 1;
    }

    std::vector<std::vector<Cut>> allCuts;
    EnumerateAllCuts(pNtk, k, allCuts);

    int maxId = Abc_NtkObjNumMax(pNtk) + 1;
    std::vector<int> cutTag(maxId, 0);
    std::vector<int> visited(maxId, 0);
    std::vector<uint64_t> nodeVal(maxId, 0);
    std::vector<Abc_Obj_t*> cone;
    cone.reserve(100);
    int travId = 0;

    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      for (const auto& cut : allCuts[id]) {
        ++travId;
        uint64_t tt = ComputeCutTruthTable(pObj, cut, travId, cutTag, visited, nodeVal, cone);
        PrintCut(id, cut);
        printf(" %llX\n", (unsigned long long)tt);
      }
    }
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt [-h] <k>\n");
  Abc_Print(-2, "\t        enumerates k-feasible cuts and computes truth tables\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG (run 'strash' first).\n");
    return 1;
  }
  if (argc - globalUtilOptind != 1) {
    goto usage;
  }
  {
    int k = atoi(argv[globalUtilOptind]);
    if (k < 2 || k > 6) {
      Abc_Print(-1, "k must be between 2 and 6.\n");
      return 1;
    }

    std::vector<std::vector<Cut>> allCuts;
    EnumerateAllCuts(pNtk, k, allCuts);

    int maxId = Abc_NtkObjNumMax(pNtk) + 1;
    std::vector<int> cutTag(maxId, 0);
    std::vector<int> visited(maxId, 0);
    std::vector<DdNode*> nodeBdd(maxId, nullptr);
    std::vector<Abc_Obj_t*> cone;
    cone.reserve(100);
    int travId = 0;

    DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);

    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      for (const auto& cut : allCuts[id]) {
        ++travId;
        int bddSize = ComputeCutBddSize(dd, pObj, cut, travId, cutTag, visited, nodeBdd, cone);
        PrintCut(id, cut);
        printf(" %d\n", bddSize);
      }
    }

    Cudd_Quit(dd);
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize [-h] <k>\n");
  Abc_Print(-2, "\t        enumerates k-feasible cuts and computes BDD size\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
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