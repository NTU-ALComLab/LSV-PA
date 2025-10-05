#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <vector>
#include <array>
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unordered_map>

// -----------------------------------------------------------------------------
// Command declarations
// -----------------------------------------------------------------------------
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv);

// -----------------------------------------------------------------------------
// ABC package registration
// -----------------------------------------------------------------------------
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// -----------------------------------------------------------------------------
// Utility: print nodes (original)
// -----------------------------------------------------------------------------
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

// -----------------------------------------------------------------------------
// Cut representation + helpers
// -----------------------------------------------------------------------------
struct Cut {
  std::array<int, 6> leaf{}; // sorted, unique leaf IDs (PIs and/or AND nodes)
  uint8_t sz = 0;
};

struct CutHash {
  size_t operator()(Cut const& c) const noexcept {
    uint64_t h = c.sz;
    for (int t = 0; t < c.sz; ++t) {
      uint64_t x = static_cast<uint32_t>(c.leaf[t]);
      h ^= x + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    }
    return static_cast<size_t>(h);
  }
};
struct CutEq {
  bool operator()(Cut const& a, Cut const& b) const noexcept {
    if (a.sz != b.sz) return false;
    for (int t = 0; t < a.sz; ++t) if (a.leaf[t] != b.leaf[t]) return false;
    return true;
  }
};

// Merge two sorted cuts a and b into out = a ∪ b (sorted, unique).
// Returns false if union exceeds K (early prune).
static bool MergeCuts(const Cut& a, const Cut& b, int K, Cut& out) {
  int i = 0, j = 0, n = 0;

  while (i < a.sz || j < b.sz) {
    int pick;
    if (j >= b.sz || (i < a.sz && a.leaf[i] < b.leaf[j])) {
      pick = a.leaf[i++];
    } else if (i >= a.sz || b.leaf[j] < a.leaf[i]) {
      pick = b.leaf[j++];
    } else {
      pick = a.leaf[i];
      i++; j++;
    }

    if (n == 0 || out.leaf[n - 1] != pick) {
      out.leaf[n++] = pick;
      if (n > K) return false;  // early prune
    }
  }
  out.sz = (uint8_t)n;
  return true;
}

// return true iff small ⊂ big (strict subset), both sorted unique
static bool IsStrictSubset(const Cut& small, const Cut& big) {
  if (small.sz >= big.sz) return false;
  int i = 0, j = 0;
  while (i < small.sz && j < big.sz) {
    if (small.leaf[i] == big.leaf[j]) { ++i; ++j; }
    else if (small.leaf[i] > big.leaf[j]) { ++j; }
    else { return false; }
  }
  return i == small.sz;
}

// drop any cut that has a proper subset present (quadratic but tiny sets)
static void ReduceIrredundant(std::vector<Cut>& cuts) {
  std::vector<char> keep(cuts.size(), 1);
  for (size_t i = 0; i < cuts.size(); ++i) if (keep[i])
    for (size_t j = 0; j < cuts.size(); ++j) if (i != j && keep[j])
      if (cuts[j].sz < cuts[i].sz && IsStrictSubset(cuts[j], cuts[i])) { keep[i] = 0; break; }
  std::vector<Cut> tmp; tmp.reserve(cuts.size());
  for (size_t i = 0; i < cuts.size(); ++i) if (keep[i]) tmp.push_back(cuts[i]);
  cuts.swap(tmp);
}

// -----------------------------------------------------------------------------
// lsv_printmocut: enumerate K-cuts (with PI and internal leaves), aggregate
// identical cuts across PO drivers, and print:
//   "<in ids...> : <root ids...>"  (one line per cut)
// -----------------------------------------------------------------------------

static int Lsv_PrintMoCut_Usage() {
  Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
  Abc_Print(-2, "       prints lines of the form:\n");
  Abc_Print(-2, "         <in 1> <in 2> ... : <out 1> <out 2> ...\n");
  Abc_Print(-2, "       where inputs are cut leaf IDs (ascending; PIs and/or AND nodes)\n");
  Abc_Print(-2, "       and outputs are IDs of PO driver nodes sharing that cut (ascending).\n");
  Abc_Print(-2, "       Primary outputs are ignored.\n");
  Abc_Print(-2, "       constraints: 3 <= k <= 6, 1 <= l <= 4 (min #outputs sharing)\n");
  Abc_Print(-2, "example: lsv_printmocut 6 2\n");
  return 1;
}

int Lsv_CommandPrintMoCut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) { Abc_Print(-1, "Empty network.\n"); return 1; }

  // Parse options first
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h': return Lsv_PrintMoCut_Usage();
      default:  return Lsv_PrintMoCut_Usage();
    }
  }

  if (argc != 3) return Lsv_PrintMoCut_Usage();

  int K = atoi(argv[1]);
  int L = atoi(argv[2]); // threshold: min #unique PO driver nodes sharing the cut
  if (K < 3 || K > 6 || L < 1 || L > 4) {
    Abc_Print(1, "Error: 3 <= k <= 6 and 1 <= l <= 4 required.\n");
    return 1;
  }

  // Per-ID storage of cut sets
  int maxId = Abc_NtkObjNumMax(pNtk) + 1;
  std::vector<std::vector<Cut>> cutsPerId(maxId);

  // Seed PIs: each PI has one trivial cut { id(PI) }
  Abc_Obj_t* pObj; int i;
  Abc_NtkForEachPi(pNtk, pObj, i) {
    Cut tr; tr.sz = 1; tr.leaf[0] = Abc_ObjId(pObj);
    cutsPerId[ Abc_ObjId(pObj) ].push_back(tr);
  }

  auto equalCut = [](const Cut& a, const Cut& b) -> bool {
    if (a.sz != b.sz) return false;
    for (int t = 0; t < a.sz; ++t) if (a.leaf[t] != b.leaf[t]) return false;
    return true;
  };

  // For each AND node v in topo order, compute its cuts from fanins
  Abc_Obj_t* v;
  Abc_NtkForEachNode(pNtk, v, i) {
    if (Abc_ObjFaninNum(v) != 2) continue; // guard

    Abc_Obj_t* u = Abc_ObjRegular( Abc_ObjFanin0(v) );
    Abc_Obj_t* w = Abc_ObjRegular( Abc_ObjFanin1(v) );
    int idu = Abc_ObjId(u);
    int idw = Abc_ObjId(w);

    const auto& Cu = cutsPerId[idu];
    const auto& Cw = cutsPerId[idw];

    std::vector<Cut> cand;
    cand.reserve(Cu.size() * Cw.size() + 2); // +2 for potential self-cut etc.

    // merged fanin cuts
    for (const auto& cu : Cu) {
      for (const auto& cw : Cw) {
        Cut merged;
        if (!MergeCuts(cu, cw, K, merged)) continue; // pruned by K
        bool dup = false;
        for (const auto& x : cand) { if (equalCut(x, merged)) { dup = true; break; } }
        if (!dup) cand.push_back(merged);
      }
    }

    // >>> ADD: allow internal-node leaf — unit cut {v}
    {
      Cut self; self.sz = 1; self.leaf[0] = Abc_ObjId(v);
      bool dup = false;
      for (const auto& x : cand) { if (equalCut(x, self)) { dup = true; break; } }
      if (!dup) cand.push_back(self);
    }

    // Keep only inclusion-minimal cuts (drops supersets of any smaller cut)
    ReduceIrredundant(cand);

    // Store
    cutsPerId[ Abc_ObjId(v) ].swap(cand);
  }

  // Aggregate identical cuts across outputs (outputs are PO driver node IDs)
  std::unordered_map<Cut, std::vector<int>, CutHash, CutEq> cutToRoots;

  Abc_Obj_t* po;
  Abc_NtkForEachPo(pNtk, po, i) {
    Abc_Obj_t* root = Abc_ObjRegular( Abc_ObjFanin0(po) );  // driver of PO
    int rootId = Abc_ObjId(root);
    auto const& Cs = cutsPerId[rootId];

    for (auto const& c : Cs) {
      auto& vec = cutToRoots[c];
      // insert rootId if not already present (linear check; tiny vectors)
      if (std::find(vec.begin(), vec.end(), rootId) == vec.end())
        vec.push_back(rootId);
    }
  }

  // For each cut with multiplicity >= L, print one line:
  // "<leaf ids...> : <root ids...>"
  for (auto& kv : cutToRoots) {
    auto& roots = kv.second;
    // unique + sort roots
    std::sort(roots.begin(), roots.end());
    roots.erase(std::unique(roots.begin(), roots.end()), roots.end());
    if ((int)roots.size() < L) continue;

    Cut const& c = kv.first;

    // left side: inputs (leaf IDs, already sorted)
    for (int t = 0; t < c.sz; ++t) {
      Abc_Print(1, "%d%s", c.leaf[t], (t+1<c.sz) ? " " : "");
    }

    Abc_Print(1, " : ");

    // right side: outputs (root IDs)
    for (size_t r = 0; r < roots.size(); ++r) {
      Abc_Print(1, "%d%s", roots[r], (r+1<roots.size()) ? " " : "");
    }
    Abc_Print(1, "\n");
  }

  return 0;
}
