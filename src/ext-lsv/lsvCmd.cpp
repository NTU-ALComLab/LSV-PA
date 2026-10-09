#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <vector>
#include <map>
#include <algorithm>
#include <functional>

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

void Lsv_ComputeCuts(Abc_Ntk_t* pNtk, int k, std::vector<std::vector<std::vector<int>>>& nodeCuts) {
  nodeCuts.resize(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachPi(pNtk, pObj, i) {
    nodeCuts[Abc_ObjId(pObj)].push_back({(int)Abc_ObjId(pObj)});
  }

  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    std::vector<std::vector<int>>& cuts = nodeCuts[id];
    
    cuts.push_back({id});

    Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pObj);

    for (const auto& c0 : nodeCuts[Abc_ObjId(pFanin0)]) {
      for (const auto& c1 : nodeCuts[Abc_ObjId(pFanin1)]) {
        std::vector<int> c_union;
        std::set_union(c0.begin(), c0.end(), c1.begin(), c1.end(), std::back_inserter(c_union));
        
        if (c_union.size() <= (size_t)k) {
          if (std::find(cuts.begin(), cuts.end(), c_union) == cuts.end()) {
            cuts.push_back(c_union);
          }
        }
      }
    }
  }
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (argc != 2) { Abc_Print(-2, "usage: lsv_cut_tt <k>\n"); return 1; }
  if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1; }
  if (!Abc_NtkIsStrash(pNtk)) { Abc_Print(-1, "Not AIG.\n"); return 1; }
  
  int k = atoi(argv[1]);
  if (k < 2 || k > 6) { Abc_Print(-1, "k must be between 2 and 6.\n"); return 1; }

  std::vector<std::vector<std::vector<int>>> nodeCuts;
  Lsv_ComputeCuts(pNtk, k, nodeCuts);

  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    
    for (const auto& cut : nodeCuts[id]) {
      printf("%d: ", id);
      for (size_t v = 0; v < cut.size(); ++v) {
        printf("%d%s", cut[v], (v == cut.size() - 1) ? "" : " ");
      }

      std::map<int, uint64_t> memo;
      
      uint64_t masks[6] = {
        0xAAAAAAAAAAAAAAAAULL,
        0xCCCCCCCCCCCCCCCCULL,
        0xF0F0F0F0F0F0F0F0ULL,
        0xFF00FF00FF00FF00ULL,
        0xFFFF0000FFFF0000ULL,
        0xFFFFFFFF00000000ULL
      };
      
      for (size_t v = 0; v < cut.size(); ++v) {
        memo[cut[v]] = masks[cut.size() - 1 - v];
      }

      std::function<uint64_t(Abc_Obj_t*)> eval = [&](Abc_Obj_t* pNode) -> uint64_t {
        int n_id = Abc_ObjId(pNode);
        if (memo.count(n_id)) return memo[n_id];
        if (Abc_AigNodeIsConst(pNode)) return 0ULL;
        
        uint64_t v0 = eval(Abc_ObjFanin0(pNode));
        if (Abc_ObjFaninC0(pNode)) v0 = ~v0;
        
        uint64_t v1 = eval(Abc_ObjFanin1(pNode));
        if (Abc_ObjFaninC1(pNode)) v1 = ~v1;
        
        uint64_t res = v0 & v1;
        memo[n_id] = res;
        return res;
      };

      uint64_t tt = eval(pObj);
      
      if (cut.size() < 6) {
        uint64_t valid_bits_mask = (1ULL << (1ULL << cut.size())) - 1;
        tt &= valid_bits_mask;
      }
      
      printf(": %llX\n", (unsigned long long)tt);
    }
  }
  return 0;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (argc != 2) { Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n"); return 1; }
  if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1; }
  if (!Abc_NtkIsStrash(pNtk)) { Abc_Print(-1, "Not AIG.\n"); return 1; }
  
  int k = atoi(argv[1]);
  if (k < 2 || k > 6) { Abc_Print(-1, "k must be between 2 and 6.\n"); return 1; }

  std::vector<std::vector<std::vector<int>>> nodeCuts;
  Lsv_ComputeCuts(pNtk, k, nodeCuts);

  DdManager* dd = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);

  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    for (const auto& cut : nodeCuts[id]) {
      printf("%d: ", id);
      for (size_t v = 0; v < cut.size(); ++v) {
        printf("%d%s", cut[v], (v == cut.size() - 1) ? "" : " ");
      }

      std::map<int, DdNode*> memo;
      
      for (size_t v = 0; v < cut.size(); ++v) {
        DdNode* var = Cudd_bddIthVar(dd, cut[v]);
        Cudd_Ref(var);
        memo[cut[v]] = var;
      }

      std::function<DdNode*(Abc_Obj_t*)> buildBdd = [&](Abc_Obj_t* pNode) -> DdNode* {
        int n_id = Abc_ObjId(pNode);
        if (memo.count(n_id)) return memo[n_id];
        
        if (Abc_AigNodeIsConst(pNode)) {
          DdNode* res = Cudd_ReadLogicZero(dd);
          Cudd_Ref(res);
          memo[n_id] = res;
          return res;
        }
        
        DdNode* bdd0 = buildBdd(Abc_ObjFanin0(pNode));
        DdNode* bdd1 = buildBdd(Abc_ObjFanin1(pNode));
        
        DdNode* bdd0_eff = Abc_ObjFaninC0(pNode) ? Cudd_Not(bdd0) : bdd0;
        DdNode* bdd1_eff = Abc_ObjFaninC1(pNode) ? Cudd_Not(bdd1) : bdd1;
        
        DdNode* res = Cudd_bddAnd(dd, bdd0_eff, bdd1_eff);
        Cudd_Ref(res);
        
        memo[n_id] = res;
        return res;
      };

      DdNode* out = buildBdd(pObj);
      int size = Cudd_DagSize(out);
      
      printf(": %d\n", size);

      for (auto& pair : memo) {
        Cudd_RecursiveDeref(dd, pair.second);
      }
    }
  }

  Cudd_Quit(dd);
  return 0;
}

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