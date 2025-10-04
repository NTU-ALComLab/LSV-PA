#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <algorithm>
#include <array>
#include <map>
#include <optional>
#include <string>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut , 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

#define LSV_KMAX 6

class Lsv_Cut {
 public:
  unsigned num_leaves;
  std::array<unsigned int, LSV_KMAX> leaves = {}; // sorted array of leaves

  bool operator<(const Lsv_Cut& other) const {
    return leaves < other.leaves;
  }
};

/* Prints a space separated list of node IDs in `cut`, with a trailing space */
void Lsv_PrintCut(const Lsv_Cut& cut) {
  for (int i = 0; i < cut.num_leaves; i++) printf("%d ", cut.leaves[i]);
}

/* Returns the union of `cut0` and `cut1` if its size is within `k` */
std::optional<Lsv_Cut> Lsv_CombineCuts(const Lsv_Cut& cut0, const Lsv_Cut& cut1, int k) {
  size_t i = 0, j = 0, n = 0;
  Lsv_Cut result;
  while (i < cut0.num_leaves || j < cut1.num_leaves) {
    if (n == k) return std::nullopt;
    if (j == cut1.num_leaves || (i < cut0.num_leaves && cut0.leaves[i] < cut1.leaves[j])) {
      result.leaves[n] = cut0.leaves[i];
      i++; n++;
    } else if (i == cut0.num_leaves || cut1.leaves[j] < cut0.leaves[i]) {
      result.leaves[n] = cut1.leaves[j];
      j++; n++;
    } else {
      result.leaves[n] = cut0.leaves[i];
      i++; j++; n++;
    }
  }
  result.num_leaves = n;
  return result;
};

/* Returns true if `cut0` is a subset of `cut1` */
bool Lsv_CutIsSubset(const Lsv_Cut& cut0, const Lsv_Cut& cut1) {
  if (cut0.num_leaves > cut1.num_leaves) return false;
  size_t i = 0, j = 0;
  while (i < cut0.num_leaves && j < cut1.num_leaves) {
    if (cut0.leaves[i] > cut1.leaves[j]) return false;
    if (cut0.leaves[i] == cut1.leaves[j]) {
      i++; j++;
    } else {
      j++;
    }
  }
  return (i == cut0.num_leaves);
};

/* Returns true if `cut` is subsumed by an element of `cut_set` */
bool Lsv_CutIsSubsumed(const Lsv_Cut& cut, const std::vector<Lsv_Cut>& cut_set) {
  for (const Lsv_Cut& check: cut_set) {
    if (Lsv_CutIsSubset(check, cut)) return true;
  }
  return false;
}

/* Adds `cut` to `cut_set`, while removing subsumed elements of `cut_set` */
void Lsv_AddCutToCutSet(const Lsv_Cut& cut, std::vector<Lsv_Cut>& cut_set) {
  size_t num_cuts = cut_set.size();
  for (size_t i = 0; i < num_cuts;) {
    if (Lsv_CutIsSubset(cut, cut_set[i])) {
      num_cuts--;
      std::swap(cut_set[i], cut_set[num_cuts]);
    }
    else i++;
  }
  cut_set.resize(num_cuts);
  cut_set.push_back(cut);
}

/* Returns the product of two sets of `k`-feasible cuts */
std::vector<Lsv_Cut> Lsv_CutSetsProduct(const std::vector<Lsv_Cut>& cut_set0, const std::vector<Lsv_Cut>& cut_set1, int k) {
  std::vector<Lsv_Cut> product = {};
  for (const Lsv_Cut& cut0: cut_set0) {
    for (const Lsv_Cut& cut1: cut_set1) {
      if (std::optional<Lsv_Cut> combined = Lsv_CombineCuts(cut0, cut1, k)) {
        if (Lsv_CutIsSubsumed(*combined, product)) continue;
        Lsv_AddCutToCutSet(*combined, product);
      }
    }
  }
  return product;
}

/* Adds a unit cut to `cut_set`, without checking subsumption */
void Lsv_AddUnitCutToCutSet(unsigned int leave_id, std::vector<Lsv_Cut>& cut_set) {
  Lsv_Cut unit;
  unit.num_leaves = 1;
  unit.leaves[0] = leave_id;
  cut_set.push_back(unit);
}

/* Builds a map of `k`-feasible cuts and output nodes in `*pNtk` */
std::multimap<Lsv_Cut, unsigned int> Lsv_BuildCutMap(Abc_Ntk_t* pNtk, unsigned int k) {
  std::vector<std::vector<Lsv_Cut>> nodes_cuts = {};
  std::multimap<Lsv_Cut, unsigned int> cut_map;
  nodes_cuts.resize(Abc_NtkObjNum(pNtk));
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPi(pNtk, pObj, i) {
    Lsv_AddUnitCutToCutSet(Abc_ObjId(pObj), nodes_cuts[Abc_ObjId(pObj)]);
  }
  Abc_NtkForEachNode(pNtk, pObj, i) {
    assert(Abc_ObjFaninNum(pObj) == 2);
    nodes_cuts[Abc_ObjId(pObj)] = Lsv_CutSetsProduct(
      nodes_cuts[Abc_ObjId(Abc_ObjFanin0(pObj))],
      nodes_cuts[Abc_ObjId(Abc_ObjFanin1(pObj))], k
    );
    Lsv_AddUnitCutToCutSet(Abc_ObjId(pObj), nodes_cuts[Abc_ObjId(pObj)]);
    for (Lsv_Cut cut: nodes_cuts[Abc_ObjId(pObj)]) {
      cut_map.insert({cut, Abc_ObjId(pObj)});
    }
  }
  return cut_map;
}

/* Prints the cuts in `cut_map` with at least `l` output nodes */
void Lsv_CutMapPrintMoCut(const std::multimap<Lsv_Cut, unsigned int>& cut_map, unsigned int l) {
  if (cut_map.empty()) return;
  auto it_head = cut_map.cbegin();
  size_t num_outputs = 1;
  for (auto it_tail = std::next(it_head); it_tail != cut_map.cend(); ++it_tail) {
    if (it_tail->first.leaves == it_head->first.leaves) {
      num_outputs++;
      continue;
    }
    if (num_outputs >= l) {
      Lsv_PrintCut(it_head->first);
      printf(":");
      for (auto it_print = it_head; it_print != it_tail; ++it_print) printf(" %d", it_print->second);
      printf("\n");
    }
    it_head = it_tail;
    num_outputs = 1;
  }
  if (num_outputs >= l) {
    Lsv_PrintCut(it_head->first);
    printf(":");
    for (auto it_print = it_head; it_print != cut_map.cend(); ++it_print) printf(" %d", it_print->second);
    printf("\n");
  }
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

void Lsv_NtkPrintMoCut(Abc_Ntk_t* pNtk, unsigned int k, unsigned int l) {
  std::multimap<Lsv_Cut, unsigned int> cut_map = Lsv_BuildCutMap(pNtk, k);
  Lsv_CutMapPrintMoCut(cut_map, l);
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
  Abc_Print(-2, "\t        print the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  unsigned int k, l;
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
    Abc_Print(-1, "Printing k-l multi-output cuts is only supported for structurally hashed AIGs.\n");
    return 1;
  }
  if (argc != globalUtilOptind + 2) {
    Abc_Print(-1, "Wrong number of auguments.\n");
    goto usage;
  }
  k = std::stoi(argv[globalUtilOptind]);
  if (k < 3 || k > 6) {
    Abc_Print(-1, "k must be in 3~6. Got %d instead.\n", k);
    return 1;
  }
  l = std::stoi(argv[globalUtilOptind + 1]);
  if (l < 1 || l > 4) {
    Abc_Print(-1, "l must be in 1~4. Got %d instead.\n", l);
    return 1;
  }
  Lsv_NtkPrintMoCut(pNtk, k, l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocut [-h] <k> <l>\n");
  Abc_Print(-2, "\t        print the k-l multi-output cuts in a structurally hashed AIG\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  Abc_Print(-2, "\t<k>   : the max number of nodes in a cut (3~6)\n");
  Abc_Print(-2, "\t<l>   : the min number of output nodes for a cut (1~4)\n");
  return 1;
}
