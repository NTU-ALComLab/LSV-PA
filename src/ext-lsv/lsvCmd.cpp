#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <iterator>
#include <set>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv", Lsv_CommandCut, 0);
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

using LsvCut = std::vector<int>;
using LsvCuts = std::vector<LsvCut>;

static const LsvCuts& Lsv_EnumerateCuts(Abc_Obj_t* node, int k,
                                        std::vector<LsvCuts>& cache) {
  LsvCuts& cuts = cache[Abc_ObjId(node)];
  if (!cuts.empty()) return cuts;

  if (Abc_AigNodeIsConst(node)) {
    cuts.push_back({});
  } else {
    cuts.push_back({static_cast<int>(Abc_ObjId(node))});
    if (Abc_ObjIsNode(node)) {
      std::set<LsvCut> seen(cuts.begin(), cuts.end());
      const LsvCuts& left = Lsv_EnumerateCuts(Abc_ObjFanin0(node), k, cache);
      const LsvCuts& right = Lsv_EnumerateCuts(Abc_ObjFanin1(node), k, cache);
      for (const LsvCut& a : left) {
        for (const LsvCut& b : right) {
          LsvCut merged;
          std::set_union(a.begin(), a.end(), b.begin(), b.end(),
                         std::back_inserter(merged));
          if (merged.size() <= static_cast<size_t>(k) && seen.insert(merged).second)
            cuts.push_back(std::move(merged));
        }
      }
    }
  }
  return cuts;
}

static int Lsv_Evaluate(Abc_Obj_t* node, const LsvCut& cut, unsigned assignment) {
  auto leaf = std::lower_bound(cut.begin(), cut.end(), Abc_ObjId(node));
  if (leaf != cut.end() && *leaf == Abc_ObjId(node))
    return (assignment >> (cut.end() - leaf - 1)) & 1;
  if (Abc_AigNodeIsConst(node)) return 1;
  assert(Abc_ObjIsNode(node));
  int left = Lsv_Evaluate(Abc_ObjFanin0(node), cut, assignment) ^ Abc_ObjFaninC0(node);
  int right = Lsv_Evaluate(Abc_ObjFanin1(node), cut, assignment) ^ Abc_ObjFaninC1(node);
  return left & right;
}

#ifdef ABC_USE_CUDD
static DdNode* Lsv_BuildBdd(Abc_Obj_t* node, const LsvCut& cut, DdManager* dd) {
  auto leaf = std::lower_bound(cut.begin(), cut.end(), Abc_ObjId(node));
  if (leaf != cut.end() && *leaf == Abc_ObjId(node)) {
    DdNode* result = Cudd_bddIthVar(dd, leaf - cut.begin());
    if (result) Cudd_Ref(result);
    return result;
  }
  if (Abc_AigNodeIsConst(node)) {
    DdNode* result = Cudd_ReadOne(dd);
    Cudd_Ref(result);
    return result;
  }
  assert(Abc_ObjIsNode(node));
  DdNode* left = Lsv_BuildBdd(Abc_ObjFanin0(node), cut, dd);
  if (!left) return nullptr;
  DdNode* right = Lsv_BuildBdd(Abc_ObjFanin1(node), cut, dd);
  if (!right) {
    Cudd_RecursiveDeref(dd, left);
    return nullptr;
  }
  DdNode* result = Cudd_bddAnd(dd, Cudd_NotCond(left, Abc_ObjFaninC0(node)),
                               Cudd_NotCond(right, Abc_ObjFaninC1(node)));
  if (result) Cudd_Ref(result);
  Cudd_RecursiveDeref(dd, left);
  Cudd_RecursiveDeref(dd, right);
  return result;
}
#endif

static int Lsv_CommandCut(Abc_Frame_t* frame, int argc, char** argv) {
  if (argc != 4 || strcmp(argv[1], "cut") ||
      (strcmp(argv[2], "tt") && strcmp(argv[2], "bddsize"))) {
    Abc_Print(-2, "usage: lsv cut {tt|bddsize} <k> (2 <= k <= 6)\n");
    return 1;
  }
  char* end;
  errno = 0;
  long k = std::strtol(argv[3], &end, 10);
  if (errno || *end || k < 2 || k > 6) {
    Abc_Print(-1, "k must be an integer from 2 to 6.\n");
    return 1;
  }
  Abc_Ntk_t* network = Abc_FrameReadNtk(frame);
  if (!network || !Abc_NtkIsStrash(network)) {
    Abc_Print(-1, "Read a circuit and run strash first.\n");
    return 1;
  }

  bool bddsize = !strcmp(argv[2], "bddsize");
#ifdef ABC_USE_CUDD
  DdManager* dd = bddsize ? Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0) : nullptr;
  if (bddsize && !dd) {
    Abc_Print(-1, "Cannot initialize CUDD.\n");
    return 1;
  }
  if (dd) Cudd_AutodynDisable(dd);
#else
  if (bddsize) {
    Abc_Print(-1, "BDD support requires a build with CUDD.\n");
    return 1;
  }
#endif

  std::vector<LsvCuts> cache(Abc_NtkObjNumMax(network));
  Abc_Obj_t* node;
  int i;
  Abc_NtkForEachNode(network, node, i) {
    for (const LsvCut& cut : Lsv_EnumerateCuts(node, k, cache)) {
      printf("%d: ", Abc_ObjId(node));
      for (size_t j = 0; j < cut.size(); ++j)
        printf("%s%d", j ? " " : "", cut[j]);
      if (bddsize) {
#ifdef ABC_USE_CUDD
        DdNode* result = Lsv_BuildBdd(node, cut, dd);
        if (!result) {
          Cudd_Quit(dd);
          Abc_Print(-1, "Cannot build BDD.\n");
          return 1;
        }
        printf(": %d\n", Cudd_DagSize(result));
        Cudd_RecursiveDeref(dd, result);
#endif
      } else {
        uint64_t truth = 0;
        for (unsigned assignment = 0; assignment < (1u << cut.size()); ++assignment)
          truth |= uint64_t(Lsv_Evaluate(node, cut, assignment)) << assignment;
        printf(": %llX\n", static_cast<unsigned long long>(truth));
      }
    }
  }
#ifdef ABC_USE_CUDD
  if (dd) Cudd_Quit(dd);
#endif
  return 0;
}
