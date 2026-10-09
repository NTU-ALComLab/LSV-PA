#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <algorithm>
#include <cstdint>
#include <map>
#include <set>
#include <vector>
#include <cstdlib>
#include "bdd/cudd/cudd.h"
#include <functional>
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(
    Abc_Frame_t* pAbc,
    int argc,
    char** argv);
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);
  Cmd_CommandAdd(
      pAbc,
      "LSV",
      "lsv_cut_bddsize",
      Lsv_CommandCutBddSize,
      0);
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
struct LsvCut {
  std::vector<int> leaves;
};

struct LsvCutLess {
  bool operator()(const LsvCut& a, const LsvCut& b) const {
    return a.leaves < b.leaves;
  }
};

static bool Lsv_MergeCuts(
    const LsvCut& a,
    const LsvCut& b,
    int k,
    LsvCut& result) {

  result.leaves.clear();

  size_t i = 0;
  size_t j = 0;

  while (i < a.leaves.size() || j < b.leaves.size()) {
    int value;

    if (j >= b.leaves.size()) {
      value = a.leaves[i++];
    }
    else if (i >= a.leaves.size()) {
      value = b.leaves[j++];
    }
    else if (a.leaves[i] < b.leaves[j]) {
      value = a.leaves[i++];
    }
    else if (b.leaves[j] < a.leaves[i]) {
      value = b.leaves[j++];
    }
    else {
      value = a.leaves[i];
      ++i;
      ++j;
    }

    result.leaves.push_back(value);

    if ((int)result.leaves.size() > k)
      return false;
  }

  return true;
}

static int Lsv_EvalCut(
    Abc_Obj_t* pObj,
    const std::map<int, int>& leafValue,
    std::map<int, int>& memo) {

  int id = Abc_ObjId(pObj);

  auto it = leafValue.find(id);
  if (it != leafValue.end())
    return it->second;

  if (pObj == Abc_AigConst1(pObj->pNtk))
    return 1;

  if (Abc_ObjIsPi(pObj))
    return 0;

  auto m = memo.find(id);
  if (m != memo.end())
    return m->second;

  Abc_Obj_t* f0 = Abc_ObjFanin0(pObj);
  Abc_Obj_t* f1 = Abc_ObjFanin1(pObj);

  int v0 = Lsv_EvalCut(f0, leafValue, memo);
  int v1 = Lsv_EvalCut(f1, leafValue, memo);

  if (Abc_ObjFaninC0(pObj))
    v0 = !v0;

  if (Abc_ObjFaninC1(pObj))
    v1 = !v1;

  int value = v0 & v1;

  memo[id] = value;
  return value;
}

static uint64_t Lsv_TruthTable(
    Abc_Obj_t* pRoot,
    const LsvCut& cut) {

  int n = (int)cut.leaves.size();
  int count = 1 << n;

  uint64_t truth = 0;

  for (int assignment = 0; assignment < count; ++assignment) {

    std::map<int, int> leafValue;

    for (int i = 0; i < n; ++i) {
      int bit = (assignment >> (n - 1 - i)) & 1;
      leafValue[cut.leaves[i]] = bit;
    }

    std::map<int, int> memo;

    int value =
        Lsv_EvalCut(pRoot, leafValue, memo);

    if (value)
      truth |= (uint64_t(1) << assignment);
  }

  return truth;
}

static void Lsv_PrintCuts(
    Abc_Ntk_t* pNtk,
    int k) {

  std::map<int, std::vector<LsvCut> > allCuts;

  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachPi(pNtk, pObj, i) {

    LsvCut cut;
    cut.leaves.push_back(Abc_ObjId(pObj));

    allCuts[Abc_ObjId(pObj)].push_back(cut);
  }

  Abc_NtkForEachNode(pNtk, pObj, i) {

    int nodeId = Abc_ObjId(pObj);

    std::set<LsvCut, LsvCutLess> uniqueCuts;

    LsvCut trivial;
    trivial.leaves.push_back(nodeId);
    uniqueCuts.insert(trivial);

    Abc_Obj_t* f0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* f1 = Abc_ObjFanin1(pObj);

    int id0 = Abc_ObjId(f0);
    int id1 = Abc_ObjId(f1);

    const std::vector<LsvCut>& cuts0 = allCuts[id0];
    const std::vector<LsvCut>& cuts1 = allCuts[id1];

    for (const auto& c0 : cuts0) {
      for (const auto& c1 : cuts1) {

        LsvCut merged;

        if (Lsv_MergeCuts(c0, c1, k, merged))
          uniqueCuts.insert(merged);
      }
    }

    std::vector<LsvCut>& nodeCuts = allCuts[nodeId];

    nodeCuts.push_back(trivial);

    for (const auto& cut : uniqueCuts) {

      if (cut.leaves.size() == 1 &&
          cut.leaves[0] == nodeId)
        continue;

      nodeCuts.push_back(cut);
    }

    for (const auto& cut : nodeCuts) {

      uint64_t truth =
          Lsv_TruthTable(pObj, cut);

      printf("%d: ", nodeId);

      for (size_t j = 0; j < cut.leaves.size(); ++j) {
        if (j)
          printf(" ");

        printf("%d", cut.leaves[j]);
      }

      printf(": %llX\n",
             (unsigned long long)truth);
    }
  }
}

static int Lsv_CommandCutTT(
    Abc_Frame_t* pAbc,
    int argc,
    char** argv) {

  if (argc != 2) {
    Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
    return 1;
  }

  int k = atoi(argv[1]);

  if (k < 2 || k > 6) {
    Abc_Print(-1, "k must be between 2 and 6.\n");
    return 1;
  }

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Please run strash first.\n");
    return 1;
  }

  Lsv_PrintCuts(pNtk, k);

  return 0;
}

static void Lsv_ComputeCutsForBdd(
    Abc_Ntk_t* pNtk,
    int k,
    std::map<int, std::vector<LsvCut> >& allCuts) {

  Abc_Obj_t* pObj;
  int i;


  
  Abc_Obj_t* pConst1 = Abc_AigConst1(pNtk);

  if (pConst1 != nullptr) {
    LsvCut emptyCut;
    allCuts[Abc_ObjId(pConst1)].push_back(emptyCut);
  }


  
  Abc_NtkForEachPi(pNtk, pObj, i) {

    LsvCut cut;

    cut.leaves.push_back(
        Abc_ObjId(pObj));

    allCuts[Abc_ObjId(pObj)]
        .push_back(cut);
  }


  
  Abc_NtkForEachNode(pNtk, pObj, i) {

    int nodeId =
        Abc_ObjId(pObj);

    std::set<LsvCut, LsvCutLess> uniqueCuts;


    /* trivial cut {node} */
    LsvCut trivial;

    trivial.leaves.push_back(nodeId);

    uniqueCuts.insert(trivial);


    Abc_Obj_t* f0 =
        Abc_ObjFanin0(pObj);

    Abc_Obj_t* f1 =
        Abc_ObjFanin1(pObj);


    int id0 =
        Abc_ObjId(f0);

    int id1 =
        Abc_ObjId(f1);


    const std::vector<LsvCut>& cuts0 =
        allCuts[id0];

    const std::vector<LsvCut>& cuts1 =
        allCuts[id1];


    for (const auto& c0 : cuts0) {

      for (const auto& c1 : cuts1) {

        LsvCut merged;

        if (Lsv_MergeCuts(
                c0,
                c1,
                k,
                merged)) {

          uniqueCuts.insert(merged);
        }
      }
    }


    std::vector<LsvCut>& nodeCuts =
        allCuts[nodeId];


    
    nodeCuts.push_back(trivial);


    for (const auto& cut : uniqueCuts) {

      if (cut.leaves.size() == 1 &&
          cut.leaves[0] == nodeId) {

        continue;
      }

      nodeCuts.push_back(cut);
    }
  }
}



static DdNode* Lsv_BuildCutBdd(
    Abc_Obj_t* pRoot,
    const LsvCut& cut,
    DdManager* dd,
    std::map<int, DdNode*>& memo) {

  
  for (size_t i = 0;
       i < cut.leaves.size();
       ++i) {

    int nodeId =
        cut.leaves[i];

    DdNode* var =
        Cudd_bddIthVar(
            dd,
            (int)i);

    Cudd_Ref(var);

    memo[nodeId] = var;
  }


  std::function<DdNode*(Abc_Obj_t*)> build =
      [&](Abc_Obj_t* pObj) -> DdNode* {

    int id =
        Abc_ObjId(pObj);


    /* stop at cut leaf */
    auto it =
        memo.find(id);

    if (it != memo.end())
      return it->second;


    /* ABC AIG constant is constant-1 */
    if (pObj == Abc_AigConst1(pObj->pNtk)) {

      DdNode* one =
          Cudd_ReadOne(dd);

      Cudd_Ref(one);

      memo[id] = one;

      return one;
    }


    
    if (Abc_ObjIsPi(pObj)) {

      fprintf(
          stderr,
          "Error: reached PI %d "
          "outside cut leaves\n",
          id);

      DdNode* zero =
          Cudd_ReadLogicZero(dd);

      Cudd_Ref(zero);

      memo[id] = zero;

      return zero;
    }


    Abc_Obj_t* f0 =
        Abc_ObjFanin0(pObj);

    Abc_Obj_t* f1 =
        Abc_ObjFanin1(pObj);


    DdNode* bdd0 =
        build(f0);

    DdNode* bdd1 =
        build(f1);


    
    DdNode* effective0 =
        Abc_ObjFaninC0(pObj)
            ? Cudd_Not(bdd0)
            : bdd0;

    DdNode* effective1 =
        Abc_ObjFaninC1(pObj)
            ? Cudd_Not(bdd1)
            : bdd1;


    DdNode* result =
        Cudd_bddAnd(
            dd,
            effective0,
            effective1);

    Cudd_Ref(result);


    memo[id] = result;

    return result;
  };


  return build(pRoot);
}



static void Lsv_PrintCutBddSizes(
    Abc_Ntk_t* pNtk,
    int k) {

  std::map<int, std::vector<LsvCut> >
      allCuts;


  Lsv_ComputeCutsForBdd(
      pNtk,
      k,
      allCuts);


  Abc_Obj_t* pObj;
  int i;


  
  Abc_NtkForEachNode(pNtk, pObj, i) {

    int nodeId =
        Abc_ObjId(pObj);


    const std::vector<LsvCut>& cuts =
        allCuts[nodeId];


    for (const auto& cut : cuts) {

      DdManager* dd =
          Cudd_Init(
              0,
              0,
              CUDD_UNIQUE_SLOTS,
              CUDD_CACHE_SLOTS,
              0);


      std::map<int, DdNode*> memo;


      DdNode* root =
          Lsv_BuildCutBdd(
              pObj,
              cut,
              dd,
              memo);


      
      int size =
          Cudd_DagSize(root);



      printf(
          "%d: ",
          nodeId);


      for (size_t j = 0;
           j < cut.leaves.size();
           ++j) {

        if (j)
          printf(" ");

        printf(
            "%d",
            cut.leaves[j]);
      }


      printf(
          ": %d\n",
          size);


      /*
       * 釋放本 cut 所建立的 references。
       */
      for (auto& entry : memo) {

        Cudd_RecursiveDeref(
            dd,
            entry.second);
      }


      Cudd_Quit(dd);
    }
  }
}




static int Lsv_CommandCutBddSize(
    Abc_Frame_t* pAbc,
    int argc,
    char** argv) {

  if (argc != 2) {

    Abc_Print(
        -2,
        "usage: lsv_cut_bddsize <k>\n");

    return 1;
  }


  int k =
      atoi(argv[1]);


  if (k < 2 || k > 6) {

    Abc_Print(
        -1,
        "k must be between 2 and 6.\n");

    return 1;
  }


  Abc_Ntk_t* pNtk =
      Abc_FrameReadNtk(pAbc);


  if (!pNtk) {

    Abc_Print(
        -1,
        "Empty network.\n");

    return 1;
  }


  if (!Abc_NtkIsStrash(pNtk)) {

    Abc_Print(
        -1,
        "Please run strash first.\n");

    return 1;
  }


  Lsv_PrintCutBddSizes(
      pNtk,
      k);


  return 0;
}