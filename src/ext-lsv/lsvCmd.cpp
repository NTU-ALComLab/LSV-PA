#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <algorithm>
#include <iterator>
#include <map>
#include <set>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
}

void destroy(Abc_Frame_t* /*pAbc*/) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// -----------------------------------------------------------------------------
// Command: lsv_print_nodes (provided helper)
// -----------------------------------------------------------------------------

static void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
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
      printf("The SOP of this node:\n%s", static_cast<char*>(pObj->pData));
    }
  }
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
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

// -----------------------------------------------------------------------------
// Multi-output cut enumeration
// -----------------------------------------------------------------------------

using Cut = std::vector<unsigned>;
using CutList = std::vector<Cut>;
using CutMap = std::map<unsigned, CutList>;

struct CutLess {
  bool operator()(const Cut& lhs, const Cut& rhs) const {
    if (lhs.size() != rhs.size()) {
      return lhs.size() < rhs.size();
    }
    return std::lexicographical_compare(lhs.begin(), lhs.end(), rhs.begin(),
                                        rhs.end());
  }
};

static bool IsSubset(const Cut& candidate, const Cut& reference) {
  return std::includes(reference.begin(), reference.end(), candidate.begin(),
                       candidate.end());
}

static Cut MergeCuts(const Cut& cut0, const Cut& cut1) {
  Cut merged;
  merged.reserve(cut0.size() + cut1.size());
  std::set_union(cut0.begin(), cut0.end(), cut1.begin(), cut1.end(),
                 std::back_inserter(merged));
  return merged;
}

static CutList RemoveRedundantCuts(const CutList& cuts) {
  CutList filtered;
  for (const auto& cut : cuts) {
    bool dominated = false;
    for (const auto& existing : filtered) {
      if (IsSubset(existing, cut)) {
        dominated = true;
        break;
      }
    }
    if (dominated) {
      continue;
    }
    filtered.erase(std::remove_if(filtered.begin(), filtered.end(),
                                  [&cut](const Cut& existing) {
                                    return IsSubset(cut, existing);
                                  }),
                   filtered.end());
    filtered.push_back(cut);
  }
  return filtered;
}

static CutList EnumerateCutsForNode(Abc_Obj_t* pNode, const CutMap& cutMap,
                                    int k) {
  CutList cuts;
  unsigned nodeId = Abc_ObjId(pNode);

  Abc_Ntk_t* pNtk = Abc_ObjNtk(pNode);
  Abc_Obj_t* pConst = Abc_AigConst1(pNtk);

  if (pNode == pConst || Abc_ObjIsPi(pNode)) {
    cuts.push_back(Cut{nodeId});
    return cuts;
  }

  if (!Abc_AigNodeIsAnd(pNode)) {
    return cuts;
  }

  Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pNode);
  Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pNode);

  auto it0 = cutMap.find(Abc_ObjId(pFanin0));
  auto it1 = cutMap.find(Abc_ObjId(pFanin1));

  std::set<Cut, CutLess> uniqueCuts;
  uniqueCuts.insert(Cut{nodeId});

  if (it0 == cutMap.end() || it1 == cutMap.end()) {
    return CutList(uniqueCuts.begin(), uniqueCuts.end());
  }

  const CutList& faninCuts0 = it0->second;
  const CutList& faninCuts1 = it1->second;

  for (const auto& cut0 : faninCuts0) {
    for (const auto& cut1 : faninCuts1) {
      Cut merged = MergeCuts(cut0, cut1);
      if (merged.size() <= static_cast<size_t>(k)) {
        uniqueCuts.insert(merged);
      }
    }
  }

  CutList candidateCuts(uniqueCuts.begin(), uniqueCuts.end());
  std::sort(candidateCuts.begin(), candidateCuts.end(), CutLess());
  return RemoveRedundantCuts(candidateCuts);
}

static CutMap ComputeKFeasibleCuts(Abc_Ntk_t* pNtk, int k) {
  CutMap cutMap;

  Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
  if (pConst) {
    cutMap[Abc_ObjId(pConst)] = EnumerateCutsForNode(pConst, cutMap, k);
  }

  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachPi(pNtk, pObj, i) {
    cutMap[Abc_ObjId(pObj)] = EnumerateCutsForNode(pObj, cutMap, k);
  }

  Abc_AigForEachAnd(pNtk, pObj, i) {
    cutMap[Abc_ObjId(pObj)] = EnumerateCutsForNode(pObj, cutMap, k);
  }

  return cutMap;
}

static void PrintMultiOutputCuts(const CutMap& cutMap, Abc_Ntk_t* pNtk, int l) {
  using CutToNodes = std::map<Cut, std::vector<unsigned>, CutLess>;
  CutToNodes cutBuckets;

  Abc_Obj_t* pObj;
  int i;

  Abc_AigForEachAnd(pNtk, pObj, i) {
    unsigned nodeId = Abc_ObjId(pObj);
    auto it = cutMap.find(nodeId);
    if (it == cutMap.end()) {
      continue;
    }
    const CutList& cuts = it->second;
    for (const auto& cut : cuts) {
      auto& outputs = cutBuckets[cut];
      outputs.push_back(nodeId);
    }
  }

  for (auto& entry : cutBuckets) {
    auto& outputs = entry.second;
    std::sort(outputs.begin(), outputs.end());
    outputs.erase(std::unique(outputs.begin(), outputs.end()), outputs.end());
  }

  for (const auto& entry : cutBuckets) {
    const Cut& cut = entry.first;
    const std::vector<unsigned>& outputs = entry.second;

    if (static_cast<int>(outputs.size()) < l) {
      continue;
    }

    bool first = true;
    for (unsigned leaf : cut) {
      if (!first) {
        printf(" ");
      }
      printf("%u", leaf);
      first = false;
    }
    printf(" :");

    for (unsigned nodeId : outputs) {
      printf(" %u", nodeId);
    }
    printf("\n");
  }
}

static void Lsv_NtkPrintMoCut(Abc_Ntk_t* pNtk, int k, int l) {
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network should be strashed AIG (run 'strash' first).\n");
    return;
  }

  CutMap cutMap = ComputeKFeasibleCuts(pNtk, k);
  PrintMultiOutputCuts(cutMap, pNtk, l);
}

static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k = 0;
  int l = 0;

  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }

  if (argc != globalUtilOptind + 2) {
    Abc_Print(-1, "Wrong number of arguments.\n");
    goto usage;
  }

  k = atoi(argv[globalUtilOptind]);
  l = atoi(argv[globalUtilOptind + 1]);

  if (k < 3 || k > 6) {
    Abc_Print(-1, "Invalid parameter: k should be between 3 and 6.\n");
    return 1;
  }
  if (l < 1) {
    Abc_Print(-1, "Invalid parameter: l should be a positive integer.\n");
    return 1;
  }

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  Lsv_NtkPrintMoCut(pNtk, k, l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
  Abc_Print(-2, "\t        enumerate k-l multi-output cuts in AIG\n");
  Abc_Print(-2, "\t<k>   : cut size limit (3-6)\n");
  Abc_Print(-2, "\t<l>   : minimum number of outputs sharing the cut\n");
  return 1;
}

