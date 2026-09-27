#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iterator>
#include <memory>
#include <set>
#include <unordered_map>
#include <utility>
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

using LsvCut = std::vector<unsigned>;
using LsvCuts = std::vector<LsvCut>;

static const LsvCuts& Lsv_EnumerateCuts(Abc_Obj_t* node, int k,
                                        std::vector<LsvCuts>& cache) {
  LsvCuts& cuts = cache[Abc_ObjId(node)];
  if (!cuts.empty()) return cuts;

  // Strash normally removes constant fanins; retain support for imported AIGs.
  if (Abc_AigNodeIsConst(node)) {
    cuts.push_back({});
  } else {
    cuts.push_back({Abc_ObjId(node)});
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
      LsvCuts irredundant;
      for (const LsvCut& cut : cuts) {
        bool redundant = false;
        for (unsigned mask = 1; mask + 1 < (1u << cut.size()); ++mask) {
          LsvCut subset;
          for (size_t i = 0; i < cut.size(); ++i)
            if (mask & (1u << i)) subset.push_back(cut[i]);
          if (seen.count(subset)) {
            redundant = true;
            break;
          }
        }
        if (!redundant) irredundant.push_back(cut);
      }
      cuts.swap(irredundant);
    }
  }
  return cuts;
}

static int Lsv_LeafIndex(Abc_Obj_t* node, const LsvCut& cut) {
  auto leaf = std::lower_bound(cut.begin(), cut.end(), Abc_ObjId(node));
  return leaf != cut.end() && *leaf == Abc_ObjId(node) ? leaf - cut.begin() : -1;
}

static bool Lsv_EvaluateTruth(Abc_Obj_t* node, const LsvCut& cut, uint64_t mask,
                              std::unordered_map<unsigned, uint64_t>& cache,
                              uint64_t& truth) {
  unsigned id = Abc_ObjId(node);
  auto cached = cache.find(id);
  if (cached != cache.end()) {
    truth = cached->second;
    return true;
  }
  int index = Lsv_LeafIndex(node, cut);
  if (index >= 0) {
    truth = 0;
    for (unsigned assignment = 0; assignment < (1u << cut.size()); ++assignment)
      truth |= uint64_t((assignment >> (cut.size() - index - 1)) & 1) << assignment;
  } else if (Abc_AigNodeIsConst(node)) {
    truth = mask;
  } else {
    if (!Abc_ObjIsNode(node)) return false;
    uint64_t left, right;
    if (!Lsv_EvaluateTruth(Abc_ObjFanin0(node), cut, mask, cache, left) ||
        !Lsv_EvaluateTruth(Abc_ObjFanin1(node), cut, mask, cache, right))
      return false;
    if (Abc_ObjFaninC0(node)) left ^= mask;
    if (Abc_ObjFaninC1(node)) right ^= mask;
    truth = left & right;
  }
  cache.emplace(id, truth);
  return true;
}

#ifdef ABC_USE_CUDD
struct LsvBddDeref {
  DdManager* dd;
  void operator()(DdNode* node) const { Cudd_RecursiveDeref(dd, node); }
};
using LsvBddRef = std::unique_ptr<DdNode, LsvBddDeref>;

static DdNode* Lsv_BuildBdd(Abc_Obj_t* node, const LsvCut& cut, DdManager* dd,
                             std::unordered_map<unsigned, LsvBddRef>& cache) {
  unsigned id = Abc_ObjId(node);
  auto cached = cache.find(id);
  if (cached != cache.end()) return cached->second.get();
  int index = Lsv_LeafIndex(node, cut);
  DdNode* result;
  if (index >= 0) {
    result = Cudd_bddIthVar(dd, index);
  } else if (Abc_AigNodeIsConst(node)) {
    result = Cudd_ReadOne(dd);
  } else {
    if (!Abc_ObjIsNode(node)) return nullptr;
    DdNode* left = Lsv_BuildBdd(Abc_ObjFanin0(node), cut, dd, cache);
    if (!left) return nullptr;
    DdNode* right = Lsv_BuildBdd(Abc_ObjFanin1(node), cut, dd, cache);
    if (!right) return nullptr;
    result = Cudd_bddAnd(dd, Cudd_NotCond(left, Abc_ObjFaninC0(node)),
                         Cudd_NotCond(right, Abc_ObjFaninC1(node)));
  }
  if (result) {
    Cudd_Ref(result);
    cache.emplace(id, LsvBddRef(result, LsvBddDeref{dd}));
  }
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
  std::unique_ptr<DdManager, decltype(&Cudd_Quit)> dd(
      bddsize ? Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0) : nullptr,
      &Cudd_Quit);
  if (bddsize && !dd) {
    Abc_Print(-1, "Cannot initialize CUDD.\n");
    return 1;
  }
  if (dd) Cudd_AutodynDisable(dd.get());
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
      printf("%u: ", Abc_ObjId(node));
      for (size_t j = 0; j < cut.size(); ++j)
        printf("%s%u", j ? " " : "", cut[j]);
      if (!bddsize) {
        unsigned assignments = 1u << cut.size();
        uint64_t mask = assignments == 64 ? ~uint64_t(0) : (uint64_t(1) << assignments) - 1;
        std::unordered_map<unsigned, uint64_t> values;
        uint64_t truth;
        if (!Lsv_EvaluateTruth(node, cut, mask, values, truth)) {
          Abc_Print(-1, "Cut contains an invalid AIG node.\n");
          return 1;
        }
        printf(": %llX\n", static_cast<unsigned long long>(truth));
      }
#ifdef ABC_USE_CUDD
      else {
        std::unordered_map<unsigned, LsvBddRef> values;
        DdNode* result = Lsv_BuildBdd(node, cut, dd.get(), values);
        if (result) printf(": %d\n", Cudd_DagSize(result));
        if (!result) {
          Abc_Print(-1, "Cannot build BDD.\n");
          return 1;
        }
      }
#endif
    }
  }
  return 0;
}
