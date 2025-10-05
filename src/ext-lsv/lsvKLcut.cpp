#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <string>

static int Lsv_KLcut(Abc_Frame_t* pAbc, int argc, char** argv);

static void init_kl(Abc_Frame_t* pAbc) {
  // register the command for this file only
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_KLcut, 0);
}
static void destroy_kl(Abc_Frame_t* /*pAbc*/) {}

static Abc_FrameInitializer_t frame_initializer_kl = {init_kl, destroy_kl};

struct LsvKLcutRegistrationManager {
  LsvKLcutRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer_kl); }
};
// static lifetime, internal linkage
static LsvKLcutRegistrationManager s_lsvKLcutRegistrationManager;

// --- helpers ---------------------------------------------------------------

using Cut = std::vector<int>;               // sorted list of leaf IDs
using CutList = std::vector<Cut>;           // cuts of a node
static inline std::string keyOf(const Cut& c) {
  // Join as "id1 id2 id3"
  std::string s; s.reserve(c.size()*6);
  for (size_t i = 0; i < c.size(); ++i) {
    if (i) s.push_back(' ');
    s += std::to_string(c[i]);
  }
  return s;
}
static bool isSubset(const Cut& a, const Cut& b) {
  // returns true if a ⊆ b ; both sorted
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] == b[j]) { ++i; ++j; }
    else if (a[i] < b[j]) return false;
    else ++j;
  }
  return i == a.size();
}
static void dedupAndPrune(CutList& cuts) {
  // sort each cut, drop duplicates, remove any cut that is a superset of another cut
  for (auto& c : cuts) std::sort(c.begin(), c.end());
  std::sort(cuts.begin(), cuts.end());
  cuts.erase(std::unique(cuts.begin(), cuts.end()), cuts.end());

  // remove supersets: keep only minimal cuts
  std::vector<char> keep(cuts.size(), 1);
  for (size_t i = 0; i < cuts.size(); ++i) if (keep[i]) {
    for (size_t j = 0; j < cuts.size(); ++j) if (i != j && keep[j]) {
      // if cuts[j] ⊆ cuts[i] and strictly smaller, drop i
      if (cuts[j].size() <= cuts[i].size() && isSubset(cuts[j], cuts[i])) {
        if (!(cuts[i].size() == cuts[j].size() && cuts[i] == cuts[j])) keep[i] = 0;
        if (!keep[i]) break;
      }
    }
  }
  CutList pruned; pruned.reserve(cuts.size());
  for (size_t i = 0; i < cuts.size(); ++i) if (keep[i]) pruned.push_back(std::move(cuts[i]));
  cuts.swap(pruned);
}

// Enumerate k-feasible cuts for all CIs and AND nodes (ignoring POs as "outputs")
static void enumerateKFeasibleCuts(Abc_Ntk_t* pNtk, int K,
                                   std::vector<CutList>& cutsOfId) {
  cutsOfId.assign(Abc_NtkObjNumMax(pNtk) + 1, CutList());

  // Base cuts for CIs: {CI}
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachCi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    cutsOfId[id].push_back(Cut{ id });
  }

  // We will process AND nodes in topological order.
  // Abc_NtkForEachNode iterates AIG AND nodes in topo order for strashed nets.
  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    CutList accum;

    // Trivial cut {node} is always a cut (leaves allowed to be ANDs per PA1 simplification)
    accum.push_back(Cut{ id });

    // Combine fanin cuts
    Abc_Obj_t* f0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* f1 = Abc_ObjFanin1(pObj);
    int id0 = Abc_ObjId(Abc_ObjRegular(f0));
    int id1 = Abc_ObjId(Abc_ObjRegular(f1));
    const CutList& C0 = cutsOfId[id0];
    const CutList& C1 = cutsOfId[id1];

    for (const auto& a : C0) {
      for (const auto& b : C1) {
        // union (a ∪ b)
        Cut u; u.reserve(a.size() + b.size());
        size_t ia = 0, ib = 0;
        while (ia < a.size() || ib < b.size()) {
          int va = (ia < a.size() ? a[ia] : INT_MAX);
          int vb = (ib < b.size() ? b[ib] : INT_MAX);
          if (va == vb) { u.push_back(va); ++ia; ++ib; }
          else if (va < vb) { u.push_back(va); ++ia; }
          else { u.push_back(vb); ++ib; }
        }
        if ((int)u.size() <= K) accum.push_back(std::move(u));
      }
    }
    dedupAndPrune(accum);
    cutsOfId[id] = std::move(accum);
  }

  // Optional: also give trivial {CI} to any CI that already has it; (already added)
}

// Print k-l multi-output cuts grouped by identical leaf sets.
// "outputs" are **AND nodes only** (ignore POs as required by PA1).
static void printMultiOutputCuts(Abc_Ntk_t* pNtk, int K, int L) {
  std::vector<CutList> cutsOfId;
  enumerateKFeasibleCuts(pNtk, K, cutsOfId);

  // Build groups: cut key -> list of output node IDs (AND nodes sharing the cut)
  std::unordered_map<std::string, std::vector<int>> group;
  Abc_Obj_t* pObj;
  int i;

  Abc_NtkForEachNode(pNtk, pObj, i) { // AND nodes as outputs
    int nid = Abc_ObjId(pObj);
    for (const auto& c : cutsOfId[nid]) {
      if (c.empty() || (int)c.size() > K) continue;
      std::string key = keyOf(c);
      auto& outs = group[key];
      if (outs.empty() || outs.back() != nid) outs.push_back(nid); // already visiting nid once
    }
  }

  // Emit only groups with at least L outputs.
  // Sort outputs and print in requested format.
  for (auto& kv : group) {
    auto& outs = kv.second;
    if ((int)outs.size() < L) continue;

    std::sort(outs.begin(), outs.end());
    // print inputs
    printf("%s : ", kv.first.c_str());
    // print outputs
    for (size_t j = 0; j < outs.size(); ++j) {
      if (j) printf(" ");
      printf("%d", outs[j]);
    }
    printf("\n");
  }
}

// --- command ---------------------------------------------------------------
#include <climits>  // for INT_MAX

static int Lsv_KLcut(Abc_Frame_t* pAbc, int argc, char** argv) {
  auto printUsage = []() {
    Abc_Print(-2, "usage: lsv printmocut <k> <l> [-h]\n");
    Abc_Print(-2, "       enumerate k-l multi-output cuts in a strashed AIG\n");
    Abc_Print(-2, "       3 <= k <= 6, 1 <= l <= 4\n");
    Abc_Print(-2, "example:\n");
    Abc_Print(-2, "  abc> strash\n  abc> lsv printmocut 3 2\n");
  };

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network. Please read a netlist first.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Warning: network is not a strashed AIG. Run 'strash' first.\n");
    return 1;
  }

  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        printUsage();
        return 0;
      default:
        printUsage();
        return 1;
    }
  }

  if (argc < 3) {
    printUsage();
    return 1;
  }

  int K = atoi(argv[1]);
  int L = atoi(argv[2]);
  if (K < 3 || K > 6 || L < 1 || L > 4) {
    Abc_Print(-1, "Error: constraints must satisfy 3 <= k <= 6 and 1 <= l <= 4.\n");
    return 1;
  }

  printMultiOutputCuts(pNtk, K, L);
  return 0;
}
