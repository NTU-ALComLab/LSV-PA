#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"


//************************************************** */
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iterator>
#include <vector>


#include "bdd/cudd/cudd.h"
///************************************************** */


static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);



//************************************************** */
static int Lsv_CommandCutTT(Abc_Frame_t* frame, int argc, char** argv);

static int Lsv_CommandCutBDDSize(Abc_Frame_t* frame, int argc, char** argv);
///************************************************** */



void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);

//************************************************** */
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTT, 0);

  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBDDSize, 0);

  
///************************************************** */

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






//************************************************** */


struct MyCut { std::vector<int> leaves; };
using CutList = std::vector<MyCut>;

static MyCut MergeCuts(const MyCut& a, const MyCut& b) {
  MyCut out;
  std::set_union(a.leaves.begin(), a.leaves.end(), b.leaves.begin(),
                 b.leaves.end(), std::back_inserter(out.leaves));
  return out;
}

static bool HasCut(const CutList& cuts, const MyCut& candidate) {
  for (const MyCut& cut : cuts)
    if (cut.leaves == candidate.leaves) return true;
  return false;
}


static void BuildCuts(Abc_Obj_t* node, int k,
                      std::vector<CutList>& all,
                      std::vector<unsigned char>& visited) {
  const int id = Abc_ObjId(node);
  if (visited[id]) return;
  visited[id] = 1;
  all[id].push_back(MyCut{{id}}); 
  if (!Abc_ObjIsNode(node)) return;

  Abc_Obj_t* left = Abc_ObjFanin0(node);
  Abc_Obj_t* right = Abc_ObjFanin1(node);
  BuildCuts(left, k, all, visited);
  BuildCuts(right, k, all, visited);
  for (const MyCut& a : all[Abc_ObjId(left)]) {
    for (const MyCut& b : all[Abc_ObjId(right)]) {
      MyCut merged = MergeCuts(a, b);
      if (merged.leaves.size() <= static_cast<size_t>(k) &&
          !HasCut(all[id], merged))
        all[id].push_back(merged);
    }
  }
}


static bool EvaluateNode(Abc_Obj_t* node, const MyCut& cut, unsigned assignment) {
  int id = Abc_ObjId(node);
  auto it = std::lower_bound(cut.leaves.begin(), cut.leaves.end(), id);
  if (it != cut.leaves.end() && *it == id) {
    unsigned position = static_cast<unsigned>(it - cut.leaves.begin());
    unsigned shift = static_cast<unsigned>(cut.leaves.size()) - 1 - position;
    return ((assignment >> shift) & 1u) != 0;
  }

  if (!Abc_ObjIsNode(node))
    return false;
  bool a = EvaluateNode(Abc_ObjFanin0(node), cut, assignment);
  bool b = EvaluateNode(Abc_ObjFanin1(node), cut, assignment);
  if (Abc_ObjFaninC0(node)) a = !a;
  if (Abc_ObjFaninC1(node)) b = !b;
  return a && b;
}

static uint64_t GenerateTruthTable(Abc_Obj_t* root, const MyCut& cut) {
  uint64_t table = 0;
  unsigned count = 1u << cut.leaves.size(); 
  for (unsigned assignment = 0; assignment < count; ++assignment)
    if (EvaluateNode(root, cut, assignment))
      table |= (UINT64_C(1) << assignment);
  return table;
}










static DdNode* BuildBDD(DdManager* manager, uint64_t table, int numVars, int level, unsigned assignment) {


  if (level == numVars) {

    bool value = ((table >> assignment) & UINT64_C(1)) != 0;

    DdNode* terminal = value ? Cudd_ReadOne(manager) : Cudd_ReadLogicZero(manager);

    Cudd_Ref(terminal);

    return terminal;
  }


  unsigned bit = 1u << (numVars - 1 - level);

  DdNode* low = BuildBDD(manager, table, numVars, level + 1, assignment);

  if (low == nullptr)
    return nullptr;

  DdNode* high = BuildBDD(manager, table, numVars, level + 1, assignment | bit);

  if (high == nullptr) {
    Cudd_RecursiveDeref(manager, low);
    return nullptr;
  }

  DdNode* variable = Cudd_bddIthVar(manager, level);

  DdNode* result = nullptr;

  if (variable != nullptr) {
    result = Cudd_bddIte(manager, variable, high, low);
  }

  if (result != nullptr)
    Cudd_Ref(result);

  Cudd_RecursiveDeref(manager, low);
  Cudd_RecursiveDeref(manager, high);

  return result;
}






static int GenerateBDDSize(DdManager* manager, Abc_Obj_t* root, const MyCut& cut) {

  
  uint64_t table = GenerateTruthTable(root, cut);

  const int numVars = static_cast<int>(cut.leaves.size());


  DdNode* bdd = BuildBDD(manager, table, numVars, 0, 0);

  if (bdd == nullptr)
    return -1;

  int size = Cudd_DagSize(bdd);

  Cudd_RecursiveDeref(manager, bdd);

  return size;
}







static int RunCutCommand(Abc_Frame_t* frame, int argc, char** argv, bool isBDD) {


  if (argc != 2) {

    if (isBDD) {
      Abc_Print(-2, "usage: lsv_cut_bddsize <k>  (2 <= k <= 6)\n");
    } else {
      Abc_Print(-2, "usage: lsv_cut_tt <k>  (2 <= k <= 6)\n");
    }

    return 1;
  }


  char* end = nullptr;
  long kLong = strtol(argv[1], &end, 10);

  if (!argv[1][0] || *end != '\0' || kLong < 2 || kLong > 6) {

    Abc_Print(-1, "k must be an integer between 2 and 6.\n");

    return 1;
  }

  int k = static_cast<int>(kLong);

  Abc_Ntk_t* ntk = Abc_FrameReadNtk(frame);

  if (ntk == nullptr) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

 
  if (!Abc_NtkIsStrash(ntk)) {
    Abc_Print(-1, "Network must be a strashed AIG. Run strash first.\n");

    return 1;
  }



  const int n = Abc_NtkObjNumMax(ntk);

  std::vector<CutList> all(n);
  std::vector<unsigned char> visited(n, 0);

  Abc_Obj_t* node;
  int i;

  Abc_NtkForEachNode(ntk, node, i) {
    BuildCuts(node, k, all, visited);
  }


  DdManager* manager = nullptr;

  if (isBDD) {

    manager = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);

    if (manager == nullptr) {
      Abc_Print(-1, "Failed to initialize CUDD manager.\n");

      return 1;
    }
  }



  bool failed = false;

  Abc_NtkForEachNode(ntk, node, i) {

    const int rootId = Abc_ObjId(node);

    for (const MyCut& cut : all[rootId]) {

      if (isBDD) {

        int size = GenerateBDDSize(manager, node, cut);

        if (size < 0) {
          Abc_Print(-1, "Failed to build BDD.\n");
          failed = true;
          break;
        }

        printf("%d:", rootId);

        for (int id : cut.leaves) {
          printf(" %d", id);
        }

        printf(": %d\n", size);

      } else {

        uint64_t table = GenerateTruthTable(node, cut);

        printf("%d:", rootId);

        for (int id : cut.leaves) {
          printf(" %d", id);
        }

        printf(": %llX\n",
               (unsigned long long)table);
      }
    }

    if (failed)
      break;
  }

  if (manager != nullptr) {
    Cudd_Quit(manager);
  }

  return failed ? 1 : 0;
}




static int Lsv_CommandCutTT(Abc_Frame_t* frame, int argc, char** argv) {

  return RunCutCommand(frame, argc, argv, false);
}


static int Lsv_CommandCutBDDSize(Abc_Frame_t* frame, int argc, char** argv) {

  return RunCutCommand( frame, argc, argv, true);
}



///************************************************** */