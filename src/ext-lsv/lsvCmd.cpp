#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"
#include "sat/cadical/cadicalSolver.h"
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
#include "sat/satoko/satoko.h"
#include "sat/glucose/AbcGlucose.h"

#include <sys/mman.h>

#include <algorithm>
#include <functional>
#include <array>
#include <atomic>
#include <cerrno>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <memory>
#include <random>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include <poll.h>
#ifdef __linux__
#include <sched.h>
#include <sys/prctl.h>
#endif
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

extern "C" {
Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandKlFlex(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_kl_flex", Lsv_CommandKlFlex, 0);
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

static int Lsv_CommandCut(Abc_Frame_t* frame, int argc, char** argv,
                          bool bddsize) {
  if (argc != 2) {
    Abc_Print(-2, "usage: %s <k> (2 <= k <= 6)\n", argv[0]);
    return 1;
  }
  char* end;
  errno = 0;
  long k = std::strtol(argv[1], &end, 10);
  if (errno || *end || k < 2 || k > 6) {
    Abc_Print(-1, "k must be an integer from 2 to 6.\n");
    return 1;
  }
  Abc_Ntk_t* network = Abc_FrameReadNtk(frame);
  if (!network || !Abc_NtkIsStrash(network)) {
    Abc_Print(-1, "Read a circuit and run strash first.\n");
    return 1;
  }

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

static int Lsv_CommandCutTt(Abc_Frame_t* frame, int argc, char** argv) {
  return Lsv_CommandCut(frame, argc, argv, false);
}

static int Lsv_CommandCutBddSize(Abc_Frame_t* frame, int argc, char** argv) {
  return Lsv_CommandCut(frame, argc, argv, true);
}

// ---------------------------------------------------------------------------
// PA2: lsv_kl_flex <k> <l>
//
// A KL cut is identified with its region S = roots + interior; U = fanins of S
// outside S. Every node of S with a fanout outside S (incl. POs) must be a root
// (K4), and adding any other node of S as a root keeps U and S unchanged. So we
// search only "base" cuts whose roots are exactly those output nodes, run SAT
// once per base cut, and derive the cuts with extra roots from it: the extra
// roots are invisible outside S, so their bits of c are free.
//
// In a KL cut, the leaves first hit from each root form an irredundant cut of
// that root, so each cut is generated exactly once by picking, for distinct
// roots, one PA1 cut each, and requiring that no leaf lies inside another
// root's region (else the first-hit sets would differ).
//
// A(u) per base cut (Lsv_KlFlex), cheapest first; only "not allowed" is ever
// concluded without a proof, from a concrete input pattern:
//   1. Simulation (random, biased, and the counterexamples all cuts share
//      through LsvCexPool) finds the produced u, their root values cu and
//      most c a PO observes. SAT finds a pattern for the u simulation missed.
//   2. Cuts whose roots are gated by PI literals (Lsv_KlGateCube) are split
//      into disjoint cases over those literals (Lsv_KlChain); fixed PIs fold
//      most cases away in strash, the rest are small SAT calls (Lsv_KlCase).
//   3. Otherwise an incremental sweep (LsvKlSat) proves original and flipped
//      copy equal node by node under the care set U = u.
//   4. Leftovers: a race of exact engines (Lsv_Race).
// Cuts and queries run in forked children (Lsv_Pool and the loop at the end).

namespace {

struct LsvKlPair {
  unsigned root;
  LsvCut leaves;                 // sorted
  std::vector<unsigned> region;  // nodes visited from root, stopping at leaves
};

struct LsvKlCut {
  std::vector<unsigned> roots, leaves, region;  // all sorted
};

struct LsvKlSearch {
  Abc_Ntk_t* ntk;
  int k, l;
  std::vector<LsvKlPair> pairs;
  std::vector<std::vector<int>> byLeaf, bySize;  // pair indices, ascending
  std::vector<int> inS, inU, mark;
  std::vector<char> isRoot;
  std::vector<int> chosen;
  std::vector<unsigned> leaves;  // distinct leaves of the current union
  int stamp = 0, sizeS = 0, best = 0;
  std::vector<LsvKlCut> results;
  std::map<std::vector<unsigned>, bool> escapes;

  Abc_Obj_t* Obj(unsigned id) const { return Abc_NtkObj(ntk, id); }

  bool Fits(const LsvKlPair& p) const {
    if (isRoot[p.root] || inU[p.root]) return false;
    size_t extra = 0;
    for (unsigned x : p.leaves) {
      if (isRoot[x] || inS[x]) return false;
      if (!inU[x]) ++extra;
    }
    if (leaves.size() + extra > static_cast<size_t>(k)) return false;
    for (unsigned y : p.region)
      if (inU[y]) return false;
    return true;
  }

  void Push(int j) {
    const LsvKlPair& p = pairs[j];
    for (unsigned y : p.region)
      if (inS[y]++ == 0) ++sizeS;
    for (unsigned x : p.leaves)
      if (inU[x]++ == 0) leaves.push_back(x);
    isRoot[p.root] = 1;
    chosen.push_back(j);
  }

  void Pop() {
    const LsvKlPair& p = pairs[chosen.back()];
    chosen.pop_back();
    isRoot[p.root] = 0;
    for (unsigned x : p.leaves)
      if (--inU[x] == 0) leaves.erase(std::find(leaves.begin(), leaves.end(), x));
    for (unsigned y : p.region)
      if (--inS[y] == 0) --sizeS;
  }

  bool LeavesS(unsigned id) const {  // some fanout leaves S (or is a PO)
    Abc_Obj_t* fanout;
    int i;
    Abc_ObjForEachFanout(Obj(id), fanout, i) if (!inS[Abc_ObjId(fanout)]) return true;
    return false;
  }

  // K3: every leaf has a path to a PI that avoids the other leaves.
  bool Escapes(unsigned leaf) {
    if (Abc_ObjIsPi(Obj(leaf))) return true;
    ++stamp;
    std::vector<Abc_Obj_t*> stack{Abc_ObjFanin0(Obj(leaf)), Abc_ObjFanin1(Obj(leaf))};
    while (!stack.empty()) {
      Abc_Obj_t* t = stack.back();
      stack.pop_back();
      unsigned id = Abc_ObjId(t);
      if (inU[id] || mark[id] == stamp || Abc_AigNodeIsConst(t)) continue;
      if (Abc_ObjIsPi(t)) return true;
      mark[id] = stamp;
      stack.push_back(Abc_ObjFanin0(t));
      stack.push_back(Abc_ObjFanin1(t));
    }
    return false;
  }

  void Record() {
    for (int j : chosen)
      for (unsigned y : pairs[j].region)
        if (!isRoot[y] && LeavesS(y)) return;  // K4
    if (sizeS < best) return;
    if (sizeS > best) {
      best = sizeS;
      results.clear();
    }
    LsvKlCut cut;
    for (int j : chosen) {
      cut.roots.push_back(pairs[j].root);
      cut.region.insert(cut.region.end(), pairs[j].region.begin(), pairs[j].region.end());
    }
    cut.leaves = leaves;
    std::sort(cut.roots.begin(), cut.roots.end());
    std::sort(cut.leaves.begin(), cut.leaves.end());
    std::sort(cut.region.begin(), cut.region.end());
    cut.region.erase(std::unique(cut.region.begin(), cut.region.end()), cut.region.end());
    results.push_back(std::move(cut));
  }

  void Try(size_t j, int depth) {
    if (!Fits(pairs[j])) return;
    Push(j);
    bool ok = true;
    for (int c : chosen) ok = ok && LeavesS(pairs[c].root);  // base cut only
    if (ok) {
      // K3 depends on the leaf set only, which many root sets share.
      std::vector<unsigned> key = leaves;
      std::sort(key.begin(), key.end());
      auto it = escapes.find(key);
      if (it == escapes.end()) {
        for (size_t i = 0; ok && i < leaves.size(); ++i) ok = Escapes(leaves[i]);
        escapes.emplace(std::move(key), ok);
      } else {
        ok = it->second;
      }
    }
    // Both checks only get worse when more roots are added.
    if (ok) {
      Record();
      if (depth + 1 < l) Search(j + 1, depth + 1);
    }
    Pop();
  }

  // pairs are sorted by region size, so once this fails it fails for all later j.
  bool Hopeless(size_t j, int depth) const {
    return sizeS + static_cast<int>((l - depth) * pairs[j].region.size()) < best;
  }

  void Search(size_t start, int depth) {
    if (depth == 0) {
      for (size_t j = 0; j < pairs.size() && !Hopeless(j, 0); ++j) Try(j, 0);
      return;
    }
    // Pairs from end on are hopeless (Hopeless is monotone in j).
    int end = start;
    for (int len = (int)pairs.size() - end; len > 0;) {
      int half = len / 2;
      if (!Hopeless(end + half, depth)) end += half + 1, len -= half + 1;
      else len = half;
    }
    // The next root's cut either shares a leaf with the current leaves ...
    // (merged in ascending order, without duplicates; Try may change leaves)
    std::vector<std::pair<const int*, const int*>> runs;
    for (unsigned x : leaves) {
      const std::vector<int>& v = byLeaf[x];
      const int* b = std::lower_bound(v.data(), v.data() + v.size(), (int)start);
      const int* e = std::lower_bound(b, v.data() + v.size(), end);
      if (b < e) runs.push_back({b, e});
    }
    while (true) {
      int j = end;
      for (const auto& r : runs) if (r.first < r.second && *r.first < j) j = *r.first;
      if (j == end) break;
      for (auto& r : runs) if (r.first < r.second && *r.first == j) ++r.first;
      Try(j, depth);
    }
    // ... or is disjoint from them and small enough to fit.
    for (size_t size = 1; size + leaves.size() <= static_cast<size_t>(k); ++size) {
      const std::vector<int>& v = bySize[size];
      for (auto it = std::lower_bound(v.begin(), v.end(), (int)start); it != v.end(); ++it) {
        if (Hopeless(*it, depth)) break;
        bool disjoint = true;
        for (unsigned x : pairs[*it].leaves) disjoint = disjoint && !inU[x];
        if (disjoint) Try(*it, depth);
      }
    }
  }
};

}  // namespace

// An empty AIG whose PIs match ntk's, for the miters below.
static Abc_Ntk_t* Lsv_KlNewMiter(Abc_Ntk_t* ntk) {
  Abc_Ntk_t* mt = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
  for (int i = 0; i < Abc_NtkPiNum(ntk); ++i) Abc_NtkCreatePi(mt);
  return mt;
}

// mt as an Aig_Man_t for SAT, with po (if given) as a new output.
static Aig_Man_t* Lsv_KlToAig(Abc_Ntk_t* mt, Abc_Obj_t* po = nullptr) {
  if (po) Abc_ObjAddFanin(Abc_NtkCreatePo(mt), po);
  Abc_AigCleanup((Abc_Aig_t*)mt->pManFunc);
  Abc_NtkAddDummyPiNames(mt);
  Abc_NtkAddDummyPoNames(mt);
  return Abc_NtkToDar(mt, 0, 0);
}

// Adds to mt (whose PIs match ntk's) the miter output for (u, c): satisfiable
// iff some X with U(X) = u makes a PO of N[V <- c] differ from N. pc (by object
// id, -1 = free) fixes PIs. Mode 1 / 2 (single PO): satisfiable iff the PO of
// N[V <- cu] / N[V <- c] can be pol under U = u. With cs, copy b's roots are
// new PIs of mt ranging over cs instead of c.
static Abc_Obj_t* Lsv_KlMiter(Abc_Ntk_t* mt, Abc_Ntk_t* ntk, Vec_Ptr_t* order,
                              const LsvKlCut& cut, unsigned u, unsigned cu, unsigned c,
                              const std::vector<int>* pc = nullptr, int mode = 0, int pol = 0,
                              const std::vector<unsigned>* cs = nullptr) {
  int n = cut.leaves.size(), m = cut.roots.size();
  Abc_Aig_t* man = (Abc_Aig_t*)mt->pManFunc;
  size_t N = Abc_NtkObjNumMax(ntk);
  std::vector<Abc_Obj_t*> base(N), a(N), b(N);
  std::vector<char> tfo(N);
  Abc_Obj_t* one = Abc_AigConst1(mt);
  auto bit = [&](unsigned v, int w, int j) { return Abc_ObjNotCond(one, !((v >> (w - 1 - j)) & 1)); };
  unsigned constId = Abc_ObjId(Abc_AigConst1(ntk));
  base[constId] = a[constId] = b[constId] = one;
  Abc_Obj_t* obj;
  int i;
  Abc_NtkForEachPi(ntk, obj, i) {
    int v = pc ? (*pc)[Abc_ObjId(obj)] : -1;
    base[Abc_ObjId(obj)] = a[Abc_ObjId(obj)] = b[Abc_ObjId(obj)] =
        v < 0 ? Abc_NtkPi(mt, i) : Abc_ObjNotCond(one, !v);
  }
  for (int j = 0; j < m; ++j) tfo[cut.roots[j]] = 1;
  auto fix = [&](unsigned id) {  // constants for roots and for leaves outside the TFO
    for (int j = 0; j < m; ++j)
      if (cut.roots[j] == id) {
        a[id] = bit(cu, m, j);
        b[id] = cs ? Abc_NtkCreatePi(mt) : bit(c, m, j);
        return;
      }
    if (tfo[id]) return;
    for (int j = 0; j < n; ++j)
      if (cut.leaves[j] == id) {
        a[id] = b[id] = bit(u, n, j);
        // A PI leaf is u's bit on every X the care set admits, so the original
        // copy may fold it too; it then strashes together with a.
        if (Abc_ObjIsPi(Abc_NtkObj(ntk, id))) base[id] = a[id];
        return;
      }
  };
  Abc_NtkForEachPi(ntk, obj, i) fix(Abc_ObjId(obj));
  Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
    unsigned id = Abc_ObjId(obj), f0 = Abc_ObjFaninId0(obj), f1 = Abc_ObjFaninId1(obj);
    int c0 = Abc_ObjFaninC0(obj), c1 = Abc_ObjFaninC1(obj);
    base[id] = Abc_AigAnd(man, Abc_ObjNotCond(base[f0], c0), Abc_ObjNotCond(base[f1], c1));
    if (!tfo[id]) tfo[id] = tfo[f0] || tfo[f1];
    // Mode 1 reads only copy a, mode 2 only copy b.
    if (mode != 2) a[id] = Abc_AigAnd(man, Abc_ObjNotCond(a[f0], c0), Abc_ObjNotCond(a[f1], c1));
    if (mode != 1) b[id] = Abc_AigAnd(man, Abc_ObjNotCond(b[f0], c0), Abc_ObjNotCond(b[f1], c1));
    fix(id);
  }
  Abc_Obj_t* diff = Abc_ObjNot(one);
  Abc_NtkForEachPo(ntk, obj, i) {
    unsigned d = Abc_ObjFaninId0(obj);
    if (mode) diff = Abc_ObjNotCond((mode == 1 ? a : b)[d], Abc_ObjFaninC0(obj) ^ !pol);
    else diff = Abc_AigOr(man, diff, Abc_AigXor(man, a[d], b[d]));
  }
  Abc_Obj_t* mu = diff;
  if (cs) {
    Abc_Obj_t* in = Abc_ObjNot(one);
    for (unsigned ci : *cs) {
      Abc_Obj_t* eq = one;
      for (int j = 0; j < m; ++j)
        eq = Abc_AigAnd(man, eq, Abc_AigXor(man, b[cut.roots[j]], Abc_ObjNot(bit(ci, m, j))));
      in = Abc_AigOr(man, in, eq);
    }
    mu = Abc_AigAnd(man, mu, in);
  }
  for (int j = 0; j < n; ++j)
    mu = Abc_AigAnd(man, mu, Abc_AigXor(man, base[cut.leaves[j]], Abc_ObjNot(bit(u, n, j))));
  return mu;
}

// SAT on the single output of aig with satoko: 1 unsatisfiable, 0 satisfiable
// (the CI values in model), -1 gave up after limit conflicts (0: no limit).
static int Lsv_SatAig(Aig_Man_t* aig, int limit, std::vector<int>& model) {
  Gia_Man_t* gia = Gia_ManFromAig(aig);
  Cnf_Dat_t* cnf = (Cnf_Dat_t*)Mf_ManGenerateCnf(gia, 8, 0, 1, 0, 0);
  int nCi = Gia_ManCiNum(gia), first = cnf->nVars - nCi;  // the CIs come last
  satoko_opts_t o;
  satoko_default_opts(&o);
  o.conf_limit = limit;
  satoko_t* s = satoko_create();
  satoko_setnvars(s, cnf->nVars);  // CIs outside the cone are in no clause
  bool ok = true;
  for (int i = 0; ok && i < cnf->nClauses; ++i)
    ok = satoko_add_clause(s, cnf->pClauses[i], cnf->pClauses[i + 1] - cnf->pClauses[i]);
  satoko_configure(s, &o);
  ok = ok && satoko_simplify(s) == SATOKO_OK;
  int st = ok ? satoko_solve(s) : SATOKO_UNSAT;
  if (st == SATOKO_SAT)
    for (int i = 0; i < nCi; ++i) model.push_back(satoko_read_cex_varvalue(s, first + i));
  satoko_destroy(s);
  Cnf_DataFree(cnf);
  Gia_ManStop(gia);
  return st == SATOKO_UNSAT ? 1 : st == SATOKO_SAT ? 0 : -1;
}

// For all u at once: satisfiable iff for some u in us (u -> (v, root values))
// and some c among its values, an X in the case pc with U(X) = u makes the
// (single) PO of N[V <- c] differ from v. Leaves are not folded (u varies);
// copy b's roots are new PIs of mt.
static Abc_Obj_t* Lsv_KlMiterAll(Abc_Ntk_t* mt, Abc_Ntk_t* ntk, Vec_Ptr_t* order,
                                 const LsvKlCut& cut, const std::vector<int>& pc,
                                 const std::map<unsigned, std::pair<int, std::vector<unsigned>>>& us) {
  int n = cut.leaves.size(), m = cut.roots.size();
  Abc_Aig_t* man = (Abc_Aig_t*)mt->pManFunc;
  size_t N = Abc_NtkObjNumMax(ntk);
  std::vector<Abc_Obj_t*> base(N), b(N);
  std::vector<char> tfo(N);
  Abc_Obj_t* one = Abc_AigConst1(mt);
  auto bit = [&](unsigned v, int w, int j) { return Abc_ObjNotCond(one, !((v >> (w - 1 - j)) & 1)); };
  unsigned constId = Abc_ObjId(Abc_AigConst1(ntk));
  base[constId] = b[constId] = one;
  Abc_Obj_t* obj;
  int i;
  Abc_NtkForEachPi(ntk, obj, i) {
    int v = pc[Abc_ObjId(obj)];
    base[Abc_ObjId(obj)] = b[Abc_ObjId(obj)] = v < 0 ? Abc_NtkPi(mt, i) : Abc_ObjNotCond(one, !v);
  }
  std::vector<Abc_Obj_t*> rp(m);
  for (int j = 0; j < m; ++j) tfo[cut.roots[j]] = 1, rp[j] = Abc_NtkCreatePi(mt);
  Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
    unsigned id = Abc_ObjId(obj), f0 = Abc_ObjFaninId0(obj), f1 = Abc_ObjFaninId1(obj);
    int c0 = Abc_ObjFaninC0(obj), c1 = Abc_ObjFaninC1(obj);
    base[id] = Abc_AigAnd(man, Abc_ObjNotCond(base[f0], c0), Abc_ObjNotCond(base[f1], c1));
    if (!tfo[id]) tfo[id] = tfo[f0] || tfo[f1];
    b[id] = tfo[id] ? Abc_AigAnd(man, Abc_ObjNotCond(b[f0], c0), Abc_ObjNotCond(b[f1], c1)) : base[id];
    for (int j = 0; j < m; ++j)
      if (cut.roots[j] == id) b[id] = rp[j];
  }
  Abc_Obj_t* po = Abc_ObjNot(one);
  Abc_NtkForEachPo(ntk, obj, i) po = Abc_ObjNotCond(b[Abc_ObjFaninId0(obj)], Abc_ObjFaninC0(obj));
  Abc_Obj_t* care = Abc_ObjNot(one);
  for (const auto& e : us) {
    Abc_Obj_t* t = one;
    for (int j = 0; j < n; ++j)
      t = Abc_AigAnd(man, t, Abc_AigXor(man, base[cut.leaves[j]], Abc_ObjNot(bit(e.first, n, j))));
    Abc_Obj_t* in = Abc_ObjNot(one);
    for (unsigned ci : e.second.second) {
      Abc_Obj_t* eq = one;
      for (int j = 0; j < m; ++j) eq = Abc_AigAnd(man, eq, Abc_AigXor(man, rp[j], Abc_ObjNot(bit(ci, m, j))));
      in = Abc_AigOr(man, in, eq);
    }
    // The PO differs from v for this u.
    care = Abc_AigOr(man, care, Abc_AigAnd(man, Abc_AigAnd(man, t, in), Abc_ObjNotCond(po, e.second.first)));
  }
  return care;
}

// SAT on one Lsv_KlMiter output: 1 unsatisfiable, 0 satisfiable (cex set if
// given), -1 gave up after limit conflicts (0: no limit; negative: strash only).
static int Lsv_KlSolve(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut, unsigned u,
                       unsigned cu, unsigned c, const std::vector<int>& pc, int mode,
                       int pol, int limit, std::vector<char>* cex,
                       const std::vector<unsigned>* cs = nullptr) {
  Abc_Ntk_t* mt = Lsv_KlNewMiter(ntk);
  Abc_Obj_t* mu = Lsv_KlMiter(mt, ntk, order, cut, u, cu, c, &pc, mode, pol, cs);
  bool folded = mu == Abc_ObjNot(Abc_AigConst1(mt));
  int r = folded ? 1 : -1;  // limit < 0: strash only
  if (!folded && limit >= 0) {
    Aig_Man_t* aig = Lsv_KlToAig(mt, mu);
    // Satoko settles these about twice as fast as dsat.
    std::vector<int> model;
    r = Lsv_SatAig(aig, limit, model);
    if (r == 0 && cex)
      for (int i = 0; i < Abc_NtkPiNum(ntk); ++i) {
        int v = pc[Abc_ObjId(Abc_NtkPi(ntk, i))];
        cex->push_back(v >= 0 ? v : model[i]);
      }
    Aig_ManStop(aig);
  }
  Abc_NtkDelete(mt);
  return r;
}

// Ternary simulation of the Lsv_KlMiter output: true if constant propagation
// alone makes it 0, so strash would fold it to 0 too (strash propagates the
// same constants, and copies built from the same nodes hash together).
static bool Lsv_KlDead(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut, unsigned u,
                       unsigned cu, unsigned c, const std::vector<int>& pc) {
  int n = cut.leaves.size(), m = cut.roots.size();
  size_t N = Abc_NtkObjNumMax(ntk);
  // Per node: values (0, 1, 2 = unknown) of the original, a and b copies, and
  // whether a and b may differ.
  static std::vector<unsigned char> vo, va, vb, d, tfo;
  static std::vector<signed char> role;  // root j: j + 1, leaf j: -(j + 1)
  static std::vector<unsigned> roleKey;
  for (auto* v : {&vo, &va, &vb, &d, &tfo}) v->assign(N, 0);
  std::vector<unsigned> key(cut.leaves);
  key.insert(key.end(), cut.roots.begin(), cut.roots.end());
  key.push_back(n);
  if (key != roleKey || role.size() != N) {
    role.assign(N, 0);
    for (int j = 0; j < n; ++j) role[cut.leaves[j]] = -(j + 1);
    for (int j = 0; j < m; ++j) role[cut.roots[j]] = j + 1;
    roleKey.swap(key);
  }
  auto bit = [](unsigned v, int w, int j) { return (unsigned char)((v >> (w - 1 - j)) & 1); };
  auto And = [](unsigned char x, int cx, unsigned char y, int cy) -> unsigned char {
    if (x < 2) x ^= cx;
    if (y < 2) y ^= cy;
    return x == 0 || y == 0 ? 0 : x == 1 && y == 1 ? 1 : 2;
  };
  unsigned constId = Abc_ObjId(Abc_AigConst1(ntk));
  vo[constId] = va[constId] = vb[constId] = 1;
  Abc_Obj_t* obj;
  int i;
  Abc_NtkForEachPi(ntk, obj, i) {
    int v = pc[Abc_ObjId(obj)];
    vo[Abc_ObjId(obj)] = va[Abc_ObjId(obj)] = vb[Abc_ObjId(obj)] = v < 0 ? 2 : v;
  }
  for (int j = 0; j < m; ++j) tfo[cut.roots[j]] = 1;
  auto fix = [&](unsigned id) {  // as in Lsv_KlMiter
    int r = role[id];
    if (r > 0) {
      int j = r - 1;
      va[id] = bit(cu, m, j), vb[id] = bit(c, m, j), d[id] = va[id] != vb[id];
      return;
    }
    if (r == 0 || tfo[id]) return;
    int j = -r - 1;
    va[id] = vb[id] = bit(u, n, j), d[id] = 0;
    if (Abc_ObjIsPi(Abc_NtkObj(ntk, id))) vo[id] = va[id];
  };
  Abc_NtkForEachPi(ntk, obj, i) fix(Abc_ObjId(obj));
  Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
    unsigned id = Abc_ObjId(obj), f0 = Abc_ObjFaninId0(obj), f1 = Abc_ObjFaninId1(obj);
    int c0 = Abc_ObjFaninC0(obj), c1 = Abc_ObjFaninC1(obj);
    vo[id] = And(vo[f0], c0, vo[f1], c1);
    if (!tfo[id]) tfo[id] = tfo[f0] || tfo[f1];
    va[id] = And(va[f0], c0, va[f1], c1);
    vb[id] = And(vb[f0], c0, vb[f1], c1);
    // With both fanin pairs equal the copies hash to the same node.
    d[id] = va[id] < 2 && vb[id] < 2 ? va[id] != vb[id] : d[f0] || d[f1];
    fix(id);
  }
  unsigned char diff = 0;
  Abc_NtkForEachPo(ntk, obj, i) {
    unsigned f = Abc_ObjFaninId0(obj);
    unsigned char x = !d[f] ? 0 : va[f] < 2 && vb[f] < 2 ? 1 : 2;
    diff = diff == 1 || x == 1 ? 1 : diff == 2 || x == 2 ? 2 : 0;
  }
  if (diff == 0) return true;
  for (int j = 0; j < n; ++j)
    if (vo[cut.leaves[j]] < 2 && vo[cut.leaves[j]] != bit(u, n, j)) return true;
  return false;
}

// PI literals every X must satisfy for a difference at root r to reach a PO:
// the side inputs (outside tfoV) of r's post-dominators must be 1, and so must
// the fanins of a required 1. False if r can never be observed.
static bool Lsv_KlGateCube(Abc_Ntk_t* ntk, Vec_Ptr_t* order, unsigned r,
                           const std::vector<char>& tfoV, std::map<int, int>& cube) {
  int N = Abc_NtkObjNumMax(ntk), sink = N;  // sink: all POs
  std::vector<char> t(N, 0);
  std::vector<int> pos(N + 1, -1), ipd(N + 1, -1);
  t[r] = 1;
  Abc_Obj_t* o;
  int i;
  Vec_PtrForEachEntry(Abc_Obj_t*, order, o, i) {
    pos[Abc_ObjId(o)] = i;
    if (t[Abc_ObjFaninId0(o)] || t[Abc_ObjFaninId1(o)]) t[Abc_ObjId(o)] = 1;
  }
  pos[sink] = Vec_PtrSize(order);
  auto meet = [&](int a, int b) {  // nearest common post-dominator
    while (a != b) {
      while (pos[a] < pos[b]) a = ipd[a];
      while (pos[b] < pos[a]) b = ipd[b];
    }
    return a;
  };
  ipd[sink] = sink;
  std::vector<int> nodes;  // TFO of r (a root: an AND node), topological
  Vec_PtrForEachEntry(Abc_Obj_t*, order, o, i) if (t[Abc_ObjId(o)]) nodes.push_back(Abc_ObjId(o));
  for (size_t k = nodes.size(); k-- > 0;) {
    int v = nodes[k], d = -1;
    Abc_Obj_t* fo;
    int j;
    Abc_ObjForEachFanout(Abc_NtkObj(ntk, v), fo, j) {
      int f = Abc_ObjIsPo(fo) ? sink : (int)Abc_ObjId(fo);
      if (ipd[f] < 0) continue;  // reaches no PO
      d = d < 0 ? f : meet(d, f);
    }
    ipd[v] = d;
  }
  if (ipd[r] < 0) return false;
  std::vector<std::pair<int, int>> st;  // (node, required value)
  for (int d = ipd[r]; d != sink; d = ipd[d]) {
    o = Abc_NtkObj(ntk, d);
    if (!tfoV[Abc_ObjFaninId0(o)]) st.push_back({Abc_ObjFaninId0(o), !Abc_ObjFaninC0(o)});
    if (!tfoV[Abc_ObjFaninId1(o)]) st.push_back({Abc_ObjFaninId1(o), !Abc_ObjFaninC1(o)});
  }
  std::map<int, int> req;
  while (!st.empty()) {
    auto [v, val] = st.back();
    st.pop_back();
    auto it = req.find(v);
    if (it != req.end()) {
      if (it->second != val) return false;
      continue;
    }
    req[v] = val;
    o = Abc_NtkObj(ntk, v);
    if (Abc_ObjIsNode(o) && val) {
      st.push_back({Abc_ObjFaninId0(o), !Abc_ObjFaninC0(o)});
      st.push_back({Abc_ObjFaninId1(o), !Abc_ObjFaninC1(o)});
    }
  }
  for (auto& p : req)
    if (Abc_ObjIsPi(Abc_NtkObj(ntk, p.first))) cube[p.first] = p.second;
  return true;
}

// Value v that PO of the original network always has in a case (the PIs fixed
// by pc, -1: free) under U = u, or -1. Depends on u and pc only, not on c:
// cached by them.
typedef std::pair<unsigned, std::vector<int>> LsvKlKey;  // u and the fixed PI literals
static LsvKlKey Lsv_KlKeyOf(unsigned u, const std::vector<int>& pc) {
  LsvKlKey key{u, {}};
  for (size_t id = 0; id < pc.size(); ++id)
    if (pc[id] >= 0) key.second.push_back(2 * id + pc[id]);
  return key;
}
struct LsvKlConst {
  std::map<LsvKlKey, int> orig;                              // Lsv_KlOrigConst
  const std::vector<std::map<int, int>>* cubes = nullptr;    // gate cube of each root
  std::map<std::pair<LsvKlKey, unsigned>, std::pair<int, std::vector<char>>> cases;  // Lsv_KlCase
  std::map<std::pair<LsvKlKey, unsigned>, int> gaveUp;  // Lsv_KlCase: the largest limit that did not settle it
  std::map<unsigned, std::vector<unsigned>> cs;  // u -> the c asked about
  std::map<unsigned, unsigned> cu;               // u -> its original root values
  std::map<LsvKlKey, std::set<unsigned>> allPass;  // per case: u whose PO is constant over cs[u] and cu
  std::map<LsvKlKey, int> csPass;  // whether copy b's PO is never !v there for any of cs[u]
};
static int Lsv_KlOrigConst(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut, unsigned u,
                           unsigned cu, const std::vector<int>& pc, int limit,
                           LsvKlConst& cache) {
  LsvKlKey key = Lsv_KlKeyOf(u, pc);
  auto it = cache.orig.find(key);
  if (it != cache.orig.end()) return it->second;
  int v = -1;
  for (int pol = 1; pol >= 0 && v < 0; --pol)
    if (Lsv_KlSolve(ntk, order, cut, u, cu, cu, pc, 1, pol, limit, nullptr) == 1) v = !pol;
  return cache.orig[key] = v;
}

static int Lsv_KlCaseSolve(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut, unsigned u,
                           unsigned cu, unsigned c, const std::vector<int>& pc, int limit,
                           std::vector<char>& cex, LsvKlConst& cache, unsigned asked);

// One case: the PIs fixed by pc (-1: free). Returns 1, 0 (cex set) or -1.
// A root whose gate cube pc violates is blocked by a constant 0 on all its
// paths to the POs: its bit of c might as well be cu's, which gives the same
// miter. So the c of a case collapse to a few, and the answers are cached.
static int Lsv_KlCase(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut, unsigned u,
                      unsigned cu, unsigned c, const std::vector<int>& pc, int limit,
                      std::vector<char>& cex, LsvKlConst& cache) {
  int m = cut.roots.size();
  unsigned asked = c;
  for (int j = 0; cache.cubes && j < m; ++j)
    for (const auto& kv : (*cache.cubes)[j])
      if (pc[kv.first] >= 0 && pc[kv.first] != kv.second) {
        unsigned bit = 1u << (m - 1 - j);
        c = (c & ~bit) | (cu & bit);
        break;
      }
  if (c == cu) return 1;
  std::pair<LsvKlKey, unsigned> key{Lsv_KlKeyOf(u, pc), c};
  auto it = cache.cases.find(key);
  if (it != cache.cases.end()) {
    if (it->second.first == 0) cex = it->second.second;
    return it->second.first;
  }
  auto g = cache.gaveUp.find(key);
  if (g != cache.gaveUp.end() && g->second >= limit) return -1;
  std::vector<char> x;
  int r = Lsv_KlCaseSolve(ntk, order, cut, u, cu, c, pc, limit, x, cache, asked);
  if (r == 0) cex = x;
  if (r >= 0) cache.cases[key] = {r, x};
  else cache.gaveUp[key] = limit;
  return r;
}

// U(X) for the PI values x (pc's fixed PIs override).
static unsigned Lsv_KlLeafValue(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut,
                                const std::vector<int>& pc, const std::vector<int>& x) {
  std::vector<char> v(Abc_NtkObjNumMax(ntk));
  v[Abc_ObjId(Abc_AigConst1(ntk))] = 1;
  Abc_Obj_t* obj;
  int i;
  Abc_NtkForEachPi(ntk, obj, i) {
    int f = pc[Abc_ObjId(obj)];
    v[Abc_ObjId(obj)] = f >= 0 ? f : x[i];
  }
  Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i)
    v[Abc_ObjId(obj)] = (v[Abc_ObjFaninId0(obj)] ^ Abc_ObjFaninC0(obj)) & (v[Abc_ObjFaninId1(obj)] ^ Abc_ObjFaninC1(obj));
  unsigned u = 0;
  for (unsigned leaf : cut.leaves) u = u << 1 | v[leaf];
  return u;
}

// A random PI word: uniform, sparse or dense by word % 4. Arithmetic circuits
// hide many differences behind operands with long runs of 0s or 1s.
static uint64_t Lsv_RandWord(std::mt19937_64& rng, int word) {
  uint64_t r = rng();
  if (word % 4 == 1) r &= rng() & rng();
  if (word % 4 == 2) r |= rng() | rng();
  if (word % 4 == 3) r &= rng() & rng() & rng() & rng();
  return r;
}

// Counterexamples of one cut often show other cuts observable too: in deep
// arithmetic they lie in the same narrow region of the inputs. The cut
// children share them through a mapping made before the forks. A reader may
// see a slot half written: any pattern is a valid input, and simulation only
// records what it shows, so that is harmless.
struct LsvCexPool {
  std::atomic<unsigned> n;
  std::atomic<unsigned> sbRuns, sbHits;  // SimBiased calls, and those that observed something
  unsigned cap, nPis;
  unsigned char x[1];
};
static LsvCexPool* lsvPool = nullptr;

template <class T>
static void Lsv_PoolAdd(const std::vector<T>& x) {
  if (!lsvPool || x.size() < lsvPool->nPis) return;
  unsigned k = lsvPool->n.fetch_add(1);
  if (k >= lsvPool->cap) return;
  for (unsigned i = 0; i < lsvPool->nPis; ++i) lsvPool->x[(size_t)k * lsvPool->nPis + i] = x[i] != 0;
}

// PI words holding x in bit 0 and, in bits 1..63, neighbours of x with 1 to 3
// PIs flipped.
template <class T>
static std::vector<uint64_t> Lsv_NearWords(const std::vector<T>& x, int nPis, std::mt19937_64& rng) {
  std::vector<uint64_t> w(nPis);
  for (int i = 0; i < nPis; ++i) w[i] = x[i] ? ~uint64_t(0) : 0;
  for (int bit = 1; bit < 64; ++bit)
    for (int k = 0; k <= bit % 3; ++k) w[rng() % nPis] ^= uint64_t(1) << bit;
  return w;
}

// Simulates the original network on 64-bit words of PI values (pc's fixed PIs
// override; around x if given) and records, per u produced, which values the
// (single) PO took: obs[u] bit b = PO was b.
static void Lsv_KlSimObs(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut,
                         const std::vector<int>& pc, const std::vector<int>* x, int words,
                         std::mt19937_64& rng, std::map<unsigned, int>& obs) {
  std::vector<uint64_t> v(Abc_NtkObjNumMax(ntk));
  v[Abc_ObjId(Abc_AigConst1(ntk))] = ~uint64_t(0);
  int nPis = Abc_NtkPiNum(ntk), n = cut.leaves.size();
  Abc_Obj_t* obj;
  int i;
  for (int w = 0; w < words; ++w) {
    std::vector<uint64_t> in(nPis);
    if (x) in = Lsv_NearWords(*x, nPis, rng);
    else for (int k = 0; k < nPis; ++k) in[k] = Lsv_RandWord(rng, w);
    Abc_NtkForEachPi(ntk, obj, i) {
      int f = pc[Abc_ObjId(obj)];
      v[Abc_ObjId(obj)] = f < 0 ? in[i] : f ? ~uint64_t(0) : 0;
    }
    Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i)
      v[Abc_ObjId(obj)] = (v[Abc_ObjFaninId0(obj)] ^ (Abc_ObjFaninC0(obj) ? ~uint64_t(0) : 0)) &
                          (v[Abc_ObjFaninId1(obj)] ^ (Abc_ObjFaninC1(obj) ? ~uint64_t(0) : 0));
    Abc_Obj_t* po = Abc_NtkPo(ntk, 0);
    uint64_t pv = v[Abc_ObjFaninId0(po)] ^ (Abc_ObjFaninC0(po) ? ~uint64_t(0) : 0);
    for (int bit = 0; bit < 64; ++bit) {
      unsigned u = 0;
      for (int j = 0; j < n; ++j) u = u << 1 | ((v[cut.leaves[j]] >> bit) & 1);
      obs[u] |= 1 << ((pv >> bit) & 1);
    }
  }
}

// SAT on Lsv_KlMiterAll: 1 unsatisfiable, 0 satisfiable (model: all PIs of the
// miter, ntk's first), -1 gave up.
static int Lsv_KlSolveAll(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut,
                          const std::vector<int>& pc, int limit,
                          const std::map<unsigned, std::pair<int, std::vector<unsigned>>>& us,
                          std::vector<int>& model) {
  Abc_Ntk_t* mt = Lsv_KlNewMiter(ntk);
  Abc_Obj_t* mu = Lsv_KlMiterAll(mt, ntk, order, cut, pc, us);
  int r = 1;
  if (mu != Abc_ObjNot(Abc_AigConst1(mt))) {
    Aig_Man_t* aig = Lsv_KlToAig(mt, mu);
    r = Lsv_SatAig(aig, limit, model);
    Aig_ManStop(aig);
  }
  Abc_NtkDelete(mt);
  return r;
}

// asked: the c of the query, which c (with blocked roots reset) acts like.
static int Lsv_KlCaseSolve(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut, unsigned u,
                           unsigned cu, unsigned c, const std::vector<int>& pc, int limit,
                           std::vector<char>& cex, LsvKlConst& cache, unsigned asked) {
  if (Lsv_KlDead(ntk, order, cut, u, cu, c, pc)) return 1;
  if (Lsv_KlSolve(ntk, order, cut, u, cu, c, pc, 0, 0, -1, nullptr) == 1) return 1;
  // The set checks below hold for every c asked about with this u (cs).
  const std::vector<unsigned>& cs = cache.cs[u];
  bool inCs = std::find(cs.begin(), cs.end(), asked) != cs.end();
  if (Abc_NtkPoNum(ntk) == 1) {
    // Often the PO is the same constant for cu and every c asked about here:
    // checking that is much easier than the miter. First for all u in one call
    // (values guessed by simulation), then for this u, then for c alone.
    if (inCs) {
      LsvKlKey key = Lsv_KlKeyOf(~0u, pc);
      auto it = cache.allPass.find(key);
      if (it == cache.allPass.end()) {
        std::map<unsigned, std::pair<int, std::vector<unsigned>>> us;
        std::map<unsigned, int> obs;  // PO values seen per u (the original roots are in each set)
        std::mt19937_64 rng(7);
        Lsv_KlSimObs(ntk, order, cut, pc, nullptr, 4, rng, obs);
        // Simulation uses the original roots: a u seen with both PO values
        // has no constant original PO in this case.
        for (const auto& e : obs)
          if (e.second == 3 && cache.cs.count(e.first)) cache.orig[Lsv_KlKeyOf(e.first, pc)] = -1;
        for (const auto& e : cache.cs) {
          int o = obs.count(e.first) ? obs[e.first] : 0;
          if (o == 3) continue;  // the PO is not constant
          us[e.first] = {o == 2, e.second};
          us[e.first].second.push_back(cache.cu[e.first]);
        }
        while (!us.empty()) {
          std::vector<int> model;
          int r = Lsv_KlSolveAll(ntk, order, cut, pc, limit, us, model);
          if (r == 1) break;
          if (r < 0) { us.clear(); break; }
          unsigned w = Lsv_KlLeafValue(ntk, order, cut, pc, model);
          auto f = us.find(w);
          if (f == us.end()) { us.clear(); break; }  // cannot happen
          // The model's PO is !v; its neighbours may show more.
          obs[w] |= 1 << !f->second.first;
          std::vector<int> x(model.begin(), model.begin() + Abc_NtkPiNum(ntk));
          Lsv_KlSimObs(ntk, order, cut, pc, &x, 1, rng, obs);
          for (auto it2 = us.begin(); it2 != us.end();) {
            int o = obs.count(it2->first) ? obs[it2->first] : 0;
            if (o == 3) it2 = us.erase(it2);
            else {
              if (o) it2->second.first = o == 2;
              ++it2;
            }
          }
        }
        // Both PO values over the set: the mode-2 set check below must fail.
        for (const auto& e : obs)
          if (e.second == 3 && cache.cs.count(e.first)) cache.csPass[Lsv_KlKeyOf(e.first, pc)] = 0;
        std::set<unsigned> ok;
        for (const auto& e : us) {
          ok.insert(e.first);
          cache.orig[Lsv_KlKeyOf(e.first, pc)] = e.second.first;
        }
        it = cache.allPass.emplace(key, ok).first;
      }
      if (it->second.count(u)) return 1;
    }
    if (inCs) {
      LsvKlKey key = Lsv_KlKeyOf(u, pc);
      auto it = cache.csPass.find(key);
      if (it == cache.csPass.end()) {
        std::vector<unsigned> all = cs;
        all.push_back(cu);
        int w = -1;
        for (int pol = 1; pol >= 0 && w < 0; --pol)
          if (Lsv_KlSolve(ntk, order, cut, u, cu, c, pc, 2, pol, limit, nullptr, &all) == 1) w = !pol;
        if (w >= 0) cache.orig[key] = w;  // the original is the copy at cu
        it = cache.csPass.emplace(key, w >= 0).first;
      }
      if (it->second == 1) return 1;
    }
    int v = Lsv_KlOrigConst(ntk, order, cut, u, cu, pc, limit, cache);
    if (v >= 0 && Lsv_KlSolve(ntk, order, cut, u, cu, c, pc, 2, !v, limit, nullptr) == 1) return 1;
  }
  // The full miter, likewise once for all c asked about with this u first
  // (with c alone, that is the same call as below).
  if (inCs && cs.size() > 1) {
    LsvKlKey key = Lsv_KlKeyOf(u, pc);
    key.second.push_back(-1);
    auto it = cache.csPass.find(key);
    if (it == cache.csPass.end())
      it = cache.csPass.emplace(key, Lsv_KlSolve(ntk, order, cut, u, cu, c, pc, 0, 0, limit, nullptr, &cs) == 1).first;
    if (it->second == 1) return 1;
  }
  return Lsv_KlSolve(ntk, order, cut, u, cu, c, pc, 0, 0, limit, &cex);
}

// Decides (u, c) by splitting the inputs along chain (PI literals that gate the
// roots): case i has literals 0..i-1 true and literal i false, the last case all
// true. Fixed PIs fold most cases to constant 0 in strash; in a divider the
// difference only lives where the divisor is tiny. 1 allowed, 0 not, -1 gave up.
static int Lsv_KlChain(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut, unsigned u,
                       unsigned cu, unsigned c, const std::vector<std::pair<int, int>>& chain,
                       int limit, std::vector<char>& cex, LsvKlConst& cache) {
  int N = Abc_NtkObjNumMax(ntk), nc = chain.size(), res = 1;
  // Strash alone settles most cases when the chain gates the roots; when it
  // does not (many live cases), splitting only multiplies the work.
  std::vector<std::vector<int>> live;
  for (int i = nc; i >= 0; --i) {
    std::vector<int> pc(N, -1);
    for (int k = 0; k < i; ++k) pc[chain[k].first] = chain[k].second;
    if (i < nc) pc[chain[i].first] = !chain[i].second;
    // The cheap check first; strash still folds a few more.
    if (Lsv_KlDead(ntk, order, cut, u, cu, c, pc) ||
        Lsv_KlSolve(ntk, order, cut, u, cu, c, pc, 0, 0, -1, nullptr) == 1)
      continue;
    if (live.size() == 4) return -1;
    pc.push_back(i);
    live.push_back(pc);
  }
  for (auto& pc : live) {
    int i = pc.back();
    pc.pop_back();
    // A few free chain PIs left: enumerate them, smaller miters.
    std::vector<std::vector<int>> todo{pc};
    int nFree = nc - 1 - i;
    if (nFree > 0 && nFree <= 3)
      for (int k = i + 1; k < nc; ++k) {
        std::vector<std::vector<int>> next;
        for (auto& q : todo)
          for (int b = 0; b < 2; ++b) next.push_back(q), next.back()[chain[k].first] = b;
        todo.swap(next);
      }
    for (auto& q : todo) {
      int r = Lsv_KlCase(ntk, order, cut, u, cu, c, q, limit, cex, cache);
      if (r == 0) return 0;
      if (r < 0) res = -1;
    }
  }
  return res;
}

// One incremental solver per cut, shared by all (u, c): the original network
// plus a second copy of the TFO of V whose roots are free variables. A query
// assumes U = u on the original and V = c on the copy. If the plain "some PO
// differs" call does not settle it, sweep: walk the TFO in topological order,
// visiting only nodes with a fanin not yet proved equal, and prove each
// original/copy pair equal under the assumptions (the care set U = u). Proved
// equalities are added under an activation literal. If the unproved set dies
// out before a PO, c is allowed.
struct LsvKlSat {
  Abc_Ntk_t* ntk;
  Vec_Ptr_t* order;
  const LsvKlCut& cut;
  sat_solver* s;
  int N, mu, nVars;
  std::vector<char> tfo, isRoot;
  std::vector<int> pos;
  std::map<int, int> poXor;  // PO driver -> var of driver != copy
  unsigned polU = ~0u;
  std::vector<char> seenDiff, witness;
  std::vector<uint64_t> wO, wF;
  std::mt19937_64 rng{1};

  int F(int id) const { return tfo[id] ? N + id : id; }

  // Only the TFO of the roots in flip (bit j = root j, MSB first) is copied:
  // other roots keep their original value under U = u, so their TFO is shared.
  LsvKlSat(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut, unsigned flip)
      : ntk(ntk), order(order), cut(cut), N(Abc_NtkObjNumMax(ntk)) {
    tfo.assign(N, 0), isRoot.assign(N, 0), pos.assign(N, -1);
    int m = cut.roots.size();
    for (int j = 0; j < m; ++j) {
      isRoot[cut.roots[j]] = 1;
      if ((flip >> (m - 1 - j)) & 1) tfo[cut.roots[j]] = 1;
    }
    s = sat_solver_new();
    mu = 2 * N;
    nVars = mu + 1 + Abc_NtkPoNum(ntk);
    sat_solver_setnvars(s, nVars);
    sat_solver_add_const(s, Abc_ObjId(Abc_AigConst1(ntk)), 0);
    Abc_Obj_t* obj;
    int i;
    Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
      int id = Abc_ObjId(obj), f0 = Abc_ObjFaninId0(obj), f1 = Abc_ObjFaninId1(obj);
      int c0 = Abc_ObjFaninC0(obj), c1 = Abc_ObjFaninC1(obj);
      pos[id] = i;
      sat_solver_add_and(s, id, f0, f1, c0, c1, 0);
      // An unflipped root is forced to cu, its original value under U = u, so
      // the difference stops there.
      if (tfo[id] || isRoot[id] || !(tfo[f0] || tfo[f1])) continue;
      tfo[id] = 1;
      sat_solver_add_and(s, N + id, F(f0), F(f1), c0, c1, 0);
    }
    std::vector<lit> clause{Abc_Var2Lit(mu, 1)};
    Abc_NtkForEachPo(ntk, obj, i) {
      int d = Abc_ObjFaninId0(obj);
      if (!tfo[d]) continue;
      sat_solver_add_xor(s, mu + 1 + i, d, N + d, 0);
      poXor[d] = mu + 1 + i;
      clause.push_back(Abc_Var2Lit(mu + 1 + i, 0));
    }
    sat_solver_addclause(s, clause.data(), clause.data() + clause.size());
    sat_solver_simplify(s);
    sat_solver_bookmark(s);
  }
  ~LsvKlSat() { sat_solver_delete(s); }

  void Model(std::vector<char>& x) {
    Abc_Obj_t* pi;
    int i;
    x.clear();
    Abc_NtkForEachPi(ntk, pi, i) x.push_back(sat_solver_var_value(s, Abc_ObjId(pi)));
  }

  // Simulates x and 63 neighbours of it on both copies; among the patterns with
  // U = u, records which nodes differ. Returns whether a PO differs (cex set).
  bool Simulate(const std::vector<char>& x, unsigned u, unsigned c, std::vector<char>& cex) {
    int n = cut.leaves.size(), m = cut.roots.size(), nPis = Abc_NtkPiNum(ntk);
    std::vector<uint64_t> w = Lsv_NearWords(x, nPis, rng);
    Abc_Obj_t* obj;
    int i;
    wO[Abc_ObjId(Abc_AigConst1(ntk))] = ~uint64_t(0);
    Abc_NtkForEachPi(ntk, obj, i) wO[Abc_ObjId(obj)] = w[i];
    for (int j = 0; j < m; ++j) wF[cut.roots[j]] = (c >> (m - 1 - j)) & 1 ? ~uint64_t(0) : 0;
    auto in = [&](std::vector<uint64_t>& v, int f, int compl_) { return compl_ ? ~v[f] : v[f]; };
    Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
      int id = Abc_ObjId(obj), f0 = Abc_ObjFaninId0(obj), f1 = Abc_ObjFaninId1(obj);
      int c0 = Abc_ObjFaninC0(obj), c1 = Abc_ObjFaninC1(obj);
      wO[id] = in(wO, f0, c0) & in(wO, f1, c1);
      if (tfo[id] && !isRoot[id])
        wF[id] = in(tfo[f0] ? wF : wO, f0, c0) & in(tfo[f1] ? wF : wO, f1, c1);
    }
    uint64_t valid = ~uint64_t(0);
    for (int j = 0; j < n; ++j) valid &= (u >> (n - 1 - j)) & 1 ? wO[cut.leaves[j]] : ~wO[cut.leaves[j]];
    Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
      int id = Abc_ObjId(obj);
      if (tfo[id] && ((wO[id] ^ wF[id]) & valid)) seenDiff[id] = 1;
    }
    Abc_NtkForEachPo(ntk, obj, i) {
      int d = Abc_ObjFaninId0(obj);
      uint64_t diff = tfo[d] ? (wO[d] ^ wF[d]) & valid : 0;
      if (!diff) continue;
      int bit = 0;
      while (!((diff >> bit) & 1)) ++bit;
      cex.clear();
      for (int k = 0; k < nPis; ++k) cex.push_back((w[k] >> bit) & 1);
      return true;
    }
    return false;
  }

  int Solve(std::vector<lit>& a, int limit) {
    return sat_solver_solve(s, a.data(), a.data() + a.size(), limit, 0, 0, 0);
  }

  // 1: c is in A(u), 0: it is not, -1: gave up. u must be producible and cu its root value.
  // maxLim: the largest per-pair conflict budget to escalate to (0: unbounded).
  int Query(unsigned u, unsigned cu, unsigned c, std::vector<char>& cex, int maxLim) {
    return Query({{u, cu, c}}, cex, maxLim, nullptr);
  }

  // Several (u, cu, c) at once: 1 if every c is in its A(u) (each node pair
  // proved equal under the union of their care sets is equal under each),
  // 0 if some is not (*bad its index, cex set), -1 gave up. The copy must
  // cover the roots flipped by every item.
  int Query(const std::vector<std::array<unsigned, 3>>& items, std::vector<char>& cex,
            int maxLim, int* bad) {
    int n = cut.leaves.size(), m = cut.roots.size(), k = items.size();
    auto lits = [&](const std::array<unsigned, 3>& it) {
      std::vector<lit> a;
      for (int j = 0; j < n; ++j) a.push_back(Abc_Var2Lit(cut.leaves[j], !((it[0] >> (n - 1 - j)) & 1)));
      for (int j = 0; j < m; ++j) {
        a.push_back(Abc_Var2Lit(cut.roots[j], !((it[1] >> (m - 1 - j)) & 1)));
        a.push_back(Abc_Var2Lit(N + cut.roots[j], !((it[2] >> (m - 1 - j)) & 1)));
      }
      return a;
    };
    unsigned u = items[0][0], cu = items[0][1], c = items[0][2], flip = 0;
    for (const auto& it : items) flip |= it[1] ^ it[2];
    std::vector<lit> a;
    int first = nVars;  // with several items: a guard, then one selector each
    if (k == 1) {
      a = lits(items[0]);
    } else {
      nVars += 1 + k;
      sat_solver_setnvars(s, nVars);
      std::vector<lit> any{Abc_Var2Lit(first, 1)};
      for (int i = 0; i < k; ++i) {
        any.push_back(Abc_Var2Lit(first + 1 + i, 0));
        for (lit l : lits(items[i])) {
          lit cl[2] = {Abc_Var2Lit(first + 1 + i, 1), l};
          sat_solver_addclause(s, cl, cl + 2);
        }
      }
      sat_solver_addclause(s, any.data(), any.data() + any.size());
      a.push_back(Abc_Var2Lit(first, 0));
      polU = ~0u;
    }
    auto which = [&]() {  // the item a model belongs to
      int i = 0;
      while (k > 1 && i + 1 < k && !sat_solver_var_value(s, first + 1 + i)) ++i;
      if (bad) *bad = i;
      u = items[i][0], cu = items[i][1], c = items[i][2];
    };
    auto done = [&](int res) {
      if (k > 1) {
        sat_solver_rollback(s);
        nVars = first;
        polU = ~0u;
      }
      return res;
    };
    if (u != polU || k > 1) {
      // Decide towards a known X with U(X) = u, so models stay inside the care set.
      polU = u;
      witness.clear();
      if (Solve(a, 0) == l_True) {
        which();
        Model(witness);
        std::vector<lit> pol;
        for (int v = 0; v < N; ++v) {
          pol.push_back(Abc_Var2Lit(v, !sat_solver_var_value(s, v)));
          pol.push_back(Abc_Var2Lit(N + v, !sat_solver_var_value(s, v)));
        }
        sat_solver_set_literal_polarity(s, pol.data(), pol.size());
      }
    }
    a.push_back(Abc_Var2Lit(mu, 0));
    // One conflict: only the trivial cases settle in this first PO-differs
    // call; with more, it mostly just spends them.
    int r = Solve(a, 1);
    a.pop_back();
    if (r == l_True) which(), Model(cex);
    if (r != l_Undef) return done(r == l_False);

    int act = nVars++;
    sat_solver_setnvars(s, nVars);
    a.push_back(Abc_Var2Lit(act, 0));
    std::set<int> work;  // topological positions of nodes with an unproved fanin
    auto spread = [&](Abc_Obj_t* o) {  // returns whether o drives a PO
      bool po = false;
      Abc_Obj_t* fo;
      int i;
      Abc_ObjForEachFanout(o, fo, i) {
        if (Abc_ObjIsPo(fo)) po = true;
        else work.insert(pos[Abc_ObjId(fo)]);
      }
      return po;
    };
    auto equal = [&](int id) {  // adds original == copy under act
      lit c1[3] = {Abc_Var2Lit(act, 1), Abc_Var2Lit(id, 1), Abc_Var2Lit(N + id, 0)};
      lit c2[3] = {Abc_Var2Lit(act, 1), Abc_Var2Lit(id, 0), Abc_Var2Lit(N + id, 1)};
      sat_solver_addclause(s, c1, c1 + 3);
      sat_solver_addclause(s, c2, c2 + 3);
    };
    int result = 1;
    seenDiff.assign(N, 0);
    wO.resize(N), wF.resize(N);
    std::vector<char> x, proved(N, 0);
    if (!witness.empty() && Simulate(witness, u, c, cex)) result = 0;
    for (int j = 0; j < m && result == 1; ++j)
      if (((flip >> (m - 1 - j)) & 1) && spread(Abc_NtkObj(ntk, cut.roots[j]))) result = 0;
    // Rounds with a growing conflict budget. A pair the budget does not settle
    // is only skipped: its fanouts stay in the worklist, and often the
    // difference dies out further up anyway (e.g. absorbed by a fixed leaf).
    // Only an unsettled PO driver calls for another round; proved pairs keep
    // their clauses, so later rounds go straight to the hard part.
    const std::set<int> start = work;
    for (int lim = 20; result == 1; lim *= 10) {
      int L = !maxLim && lim > 20000 ? 0 : lim;  // 0: unbounded
      bool open = false;
      int nUnd = 0;
      work = start;
      int done = 0;  // positions below it are settled
      while (result == 1 && !work.empty()) {
        int p = *work.begin();
        work.erase(work.begin());
        // Copied nodes that never entered the worklist have only equal fanins, so
        // they are equal too; the solver has separate variables and must be told.
        for (; done < p; ++done) {
          int e = Abc_ObjId((Abc_Obj_t*)Vec_PtrEntry(order, done));
          if (tfo[e] && !isRoot[e] && !proved[e]) proved[e] = 1, equal(e);
        }
        done = p + 1;
        Abc_Obj_t* obj = (Abc_Obj_t*)Vec_PtrEntry(order, p);
        int id = Abc_ObjId(obj);
        if (isRoot[id] || proved[id]) continue;
        int res = seenDiff[id] ? l_True : l_False;
        bool po = false;
        Abc_Obj_t* fo;
        int i;
        Abc_ObjForEachFanout(obj, fo, i) po = po || Abc_ObjIsPo(fo);
        // A PO driver's pair differs iff its XOR variable is true: one call
        // for both polarities.
        auto px = poXor.find(id);
        bool one = px != poXor.end();
        for (int pol = 0; pol < 2 - one && res != l_True; ++pol) {
          if (one) a.push_back(Abc_Var2Lit(px->second, 0)), a.push_back(Abc_Var2Lit(px->second, 0));
          else a.push_back(Abc_Var2Lit(id, pol)), a.push_back(Abc_Var2Lit(N + id, !pol));
          // A PO driver gets a large budget at once: undecided, it would
          // only be redone in the next round.
          int r = Solve(a, po && L ? std::max(100000, 20 * L) : L);
          nUnd += r == l_Undef;
          a.pop_back(), a.pop_back();
          if (r != l_False) res = r;
          if (r != l_True) continue;
          // The model and its neighbours show which later nodes differ: no SAT call for those.
          which();
          Model(x);
          if (Simulate(x, u, c, cex)) result = 0;
        }
        if (res == l_False) {
          proved[id] = 1;
          equal(id);
          continue;
        }
        if (spread(obj) && result == 1) open = true;  // an unsettled PO driver
        // Undecided pairs make their whole TFO undecided too: past a few, the
        // budget is just too small, so go to the next round right away.
        if (L && nUnd > 10) {
          open = true;
          break;
        }
      }
      if (result == 1 && open) {
        if (!L || (maxLim && lim >= maxLim)) result = -1;
      } else {
        break;
      }
    }
    // Drop this query's clauses (and learnt ones): kept, the guarded clauses of
    // hundreds of queries would bog the solver down.
    sat_solver_rollback(s);
    nVars = act;
    if (k > 1) nVars = first, polU = ~0u;
    return result;
  }
};

// fork, but on Linux the child dies with its parent: a killed lsv_kl_flex
// (timeout) leaves no workers behind.
static pid_t Lsv_Fork() {
#ifdef __linux__
  pid_t parent = getpid();
#endif
  pid_t pid = fork();
#ifdef __linux__
  if (pid == 0 && (prctl(PR_SET_PDEATHSIG, SIGKILL) != 0 || getppid() != parent)) _exit(1);
#endif
  return pid;
}

// Writes all n bytes of data to fd (a child's result to its parent).
static void Lsv_WriteAll(int fd, const void* data, size_t n) {
  const char* p = (const char*)data;
  while (n) {
    ssize_t w = write(fd, p, n);
    if (w <= 0) return;
    p += w, n -= w;
  }
}

// Runs each f in its own forked child and returns the first answer; the
// others are killed. Every f is exact, so whichever finishes first is right.
// Each child leads its own process group, so the children an f forks die with
// it. done, polled twice a second, may settle the race first: it then returns
// 0 (another cut's counterexample showed it). Without fork, the first f just
// runs here.
static int Lsv_Race(const std::vector<std::function<int()>>& fs,
                    const std::function<bool()>& done = {}) {
  fflush(stdout);
  fflush(stderr);
  std::vector<pid_t> pids;
  std::vector<struct pollfd> pfds;
  for (const auto& f : fs) {
    int fd[2];
    if (pipe(fd) != 0) break;
    pid_t pid = Lsv_Fork();
    if (pid < 0) {
      close(fd[0]);
      close(fd[1]);
      break;
    }
    if (pid == 0) {
      setpgid(0, 0);
      close(fd[0]);
      int r = f();
      if (write(fd[1], &r, sizeof r) < 0) {}
      _exit(0);
    }
    setpgid(pid, pid);
    close(fd[1]);
    pids.push_back(pid);
    pfds.push_back({fd[0], POLLIN, 0});
  }
  int res = -1;
  if (pids.empty()) return fs[0]();
  size_t open = pfds.size();
  while (res < 0 && open) {
    int k = poll(pfds.data(), pfds.size(), done ? 500 : -1);
    if (k < 0) break;
    if (k == 0) {
      if (done()) res = 0;
      continue;
    }
    for (auto& p : pfds) {
      if (p.fd < 0 || !p.revents) continue;
      int r;
      if (read(p.fd, &r, sizeof r) == (ssize_t)sizeof r && r >= 0) res = r;
      close(p.fd);
      p.fd = -1;
      --open;
      if (res >= 0) break;
    }
  }
  for (size_t i = 0; i < pids.size(); ++i) {
    kill(-pids[i], SIGKILL);
    waitpid(pids[i], nullptr, 0);
    if (pfds[i].fd >= 0) close(pfds[i].fd);
  }
  return res;
}

// Runs f(0..n-1) on up to `workers` forked children, which take the next group
// of tasks from a pipe as they finish one. A task whose child dies stays -1.
static std::vector<int> Lsv_Pool(size_t n, size_t workers, const std::function<int(int)>& f,
                                 std::vector<std::vector<int>> groups = {}) {
  std::vector<int> res(n, -1);
  // Tasks of one group go to the same child, one after another.
  if (groups.empty())
    for (size_t i = 0; i < n; ++i) groups.push_back({(int)i});
  int q[2], r[2];
  if (workers < 2 || groups.size() < 2 || pipe(q) != 0) {
    for (size_t i = 0; i < n; ++i) res[i] = f(i);
    return res;
  }
  if (pipe(r) != 0) {
    close(q[0]), close(q[1]);
    for (size_t i = 0; i < n; ++i) res[i] = f(i);
    return res;
  }
  for (int g = 0; g < (int)groups.size(); ++g)  // few: fits the pipe buffer
    if (write(q[1], &g, sizeof g) < 0) {}
  close(q[1]);
  fflush(stdout);
  fflush(stderr);
  std::vector<pid_t> pids;
  for (size_t w = 0; w < std::min(workers, groups.size()); ++w) {
    pid_t pid = Lsv_Fork();
    if (pid == 0) {
      close(r[0]);
      int g;
      while (read(q[0], &g, sizeof g) == (ssize_t)sizeof g)
        for (int i : groups[g]) {
          int out[2] = {i, f(i)};
          if (write(r[1], out, sizeof out) < 0) _exit(0);
        }
      _exit(0);
    }
    if (pid > 0) pids.push_back(pid);
  }
  close(q[0]);
  close(r[1]);
  if (pids.empty()) {  // no fork: the queue is lost, do it here
    close(r[0]);
    for (size_t i = 0; i < n; ++i) res[i] = f(i);
    return res;
  }
  int out[2];
  while (read(r[0], out, sizeof out) == (ssize_t)sizeof out) res[out[0]] = out[1];
  close(r[0]);
  for (pid_t pid : pids) waitpid(pid, nullptr, 0);
  return res;
}

// e with the CIs of fix >= 0 set to those values, strashed. It keeps all CIs.
static Aig_Man_t* Lsv_KlCof(Aig_Man_t* e, const std::vector<int>& fix) {
  Aig_Man_t* d = Aig_ManStart(Aig_ManObjNumMax(e));
  Aig_ManConst1(e)->pData = Aig_ManConst1(d);
  Aig_Obj_t* o;
  int i;
  Aig_ManForEachCi(e, o, i) {
    o->pData = Aig_ObjCreateCi(d);
    if (fix[i] >= 0) o->pData = Aig_NotCond(Aig_ManConst1(d), !fix[i]);
  }
  Aig_ManForEachNode(e, o, i) o->pData = Aig_And(d, Aig_ObjChild0Copy(o), Aig_ObjChild1Copy(o));
  Aig_ManForEachCo(e, o, i) Aig_ObjCreateCo(d, Aig_ObjChild0Copy(o));
  Aig_ManCleanup(d);
  return d;
}

static bool Lsv_KlIsZero(Aig_Man_t* e) {
  return Aig_ObjChild0(Aig_ManCo(e, 0)) == Aig_ManConst0(e);
}

// Splits the single output of e (consumed) into cubes that are satisfiable
// iff e is. First every CI whose one cofactor folds to constant 0 is fixed to
// the other value (any satisfying input has it); then, `depth` times, e splits
// on the CI whose larger cofactor is smallest. In deep arithmetic, a value of
// one input often folds a large part of the logic: the cubes are smaller and
// together much easier than e for SAT.
// fixed: the CI values fixed so far; each cube comes with its own.
typedef std::pair<Aig_Man_t*, std::vector<int>> LsvKlCube;
static void Lsv_KlCubes(Aig_Man_t* e, int depth, std::vector<LsvKlCube>& cubes,
                        std::vector<int> fixed = {}) {
  fixed.resize(Aig_ManCiNum(e), -1);
  while (!Lsv_KlIsZero(e)) {
    int nCi = Aig_ManCiNum(e), best = -1, bestSize = INT_MAX;
    std::vector<int> fix(nCi, -1), implied(nCi, -1);
    bool any = false;
    for (int v = 0; v < nCi; ++v) {
      if (Aig_ObjRefs(Aig_ManCi(e, v)) == 0) continue;
      int size[2];
      for (int b = 0; b < 2; ++b) {
        fix[v] = b;
        Aig_Man_t* d = Lsv_KlCof(e, fix);
        size[b] = Lsv_KlIsZero(d) ? 0 : Aig_ManNodeNum(d) + 1;
        Aig_ManStop(d);
      }
      fix[v] = -1;
      if (!size[0] && !size[1]) {  // both fold: e is constant 0
        Aig_ManStop(e);
        return;
      }
      if (!size[0] || !size[1]) implied[v] = !size[0], any = true;
      if (std::max(size[0], size[1]) < bestSize) bestSize = std::max(size[0], size[1]), best = v;
    }
    if (!any && (depth == 0 || best < 0)) {
      cubes.push_back({e, fixed});
      return;
    }
    if (any) {
      for (int v = 0; v < nCi; ++v)
        if (implied[v] >= 0) fixed[v] = implied[v];
      Aig_Man_t* d = Lsv_KlCof(e, implied);
      Aig_ManStop(e);
      e = d;
      continue;
    }
    for (int b = 0; b < 2; ++b) {
      fix[best] = fixed[best] = b;
      Lsv_KlCubes(Lsv_KlCof(e, fix), depth - 1, cubes, fixed);
    }
    Aig_ManStop(e);
    return;
  }
  Aig_ManStop(e);
}

// Unbounded CaDiCaL on the output of cube e: 1 SAT (its input, with the
// cube's fixed values, goes to the shared pool), 0 UNSAT.
static int Lsv_KlCadical(const LsvKlCube& cube) {
  Aig_Man_t* e = cube.first;
  Cnf_Dat_t* cnf = Cnf_Derive(e, 1);
  cadical_solver* cs = cadical_solver_new();
  cadical_solver_setnvars(cs, cnf->nVars);
  int *beg, *end, k, unsat = 0;
  Cnf_CnfForClause(cnf, beg, end, k) if (!unsat && !cadical_solver_addclause(cs, beg, end)) unsat = 1;
  int l = Abc_Var2Lit(cnf->pVarNums[Aig_ManCo(e, 0)->Id], 0);
  int r = unsat ? -1 : cadical_solver_solve(cs, &l, &l + 1, 0, 0, 0, 0);
  if (r == 1) {
    std::vector<int> x = cube.second;
    Aig_Obj_t* ci;
    Aig_ManForEachCi(e, ci, k) if (x[k] < 0) {
      int v = cnf->pVarNums[ci->Id];
      x[k] = v >= 0 && cadical_solver_get_var_value(cs, v) > 0;
    }
    Lsv_PoolAdd(x);
  }
  cadical_solver_delete(cs);
  Cnf_DataFree(cnf);
  return r == 1;
}

// Whether c is in A(u), by CaDiCaL on the miter: split into up to 2^depth
// cubes (Lsv_KlCubes) solved on `workers` children, or whole with depth < 0.
// Returns 1 (allowed), 0 (not) or -1 (a child died).
static int Lsv_KlCadicalMiter(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut,
                              unsigned u, unsigned cu, unsigned c, int depth, size_t workers) {
  Abc_Ntk_t* mt = Lsv_KlNewMiter(ntk);
  Abc_Obj_t* mu = Lsv_KlMiter(mt, ntk, order, cut, u, cu, c);
  if (mu == Abc_ObjNot(Abc_AigConst1(mt))) {
    Abc_NtkDelete(mt);
    return 1;
  }
  std::vector<LsvKlCube> cubes;
  Aig_Man_t* aig = Lsv_KlToAig(mt, mu);
  if (depth < 0) cubes.push_back({aig, std::vector<int>(Aig_ManCiNum(aig), -1)});
  else Lsv_KlCubes(aig, depth, cubes);
  Abc_NtkDelete(mt);
  std::vector<int> r = Lsv_Pool(cubes.size(), workers, [&](int i) { return Lsv_KlCadical(cubes[i]); });
  for (auto& cb : cubes) Aig_ManStop(cb.first);
  int allowed = 1;
  for (int x : r)
    if (x == 1) return 0;
    else if (x < 0) allowed = -1;
  return allowed;
}

// A(u) for one base cut, cheapest step first (see the overview at the top of
// PA2). masks[u] is A(u) as a bit mask over the root values c.
struct LsvKlFlex {
  typedef std::array<unsigned, 3> Item;  // (u, cu, c): is c in A(u)? cu: u's original root values
  Abc_Ntk_t* ntk;
  Vec_Ptr_t* order;
  const LsvKlCut& cut;
  size_t workers;
  int n, m, N, nPis;
  unsigned full;
  std::vector<unsigned> masks;

  // The miter of the spec as an AIG. CIs: the PIs, then the forced root values
  // p. COs: the leaves, mu, then the original roots.
  Aig_Man_t* aig = nullptr;
  std::vector<char> tfo;      // TFO of V in ntk
  std::vector<int> rootTfo;   // AIG nodes that depend on p, topological
  // Gate cube of each root, and the chain of their PI literals, highest PI first.
  std::vector<std::map<int, int>> cubes;
  std::vector<std::pair<int, int>> chain;

  // Simulation results per u: produced, its root values, the c a PO observed,
  // and an input pattern with U = u.
  std::vector<char> seen;
  std::vector<unsigned> orig_c, observed;
  std::vector<std::vector<char>> point;
  std::vector<uint64_t> val;  // simulation words of the AIG nodes
  long gain = 0;              // new facts found by simulation
  std::mt19937_64 rng{1};

  std::map<unsigned, std::unique_ptr<LsvKlSat>> sweeps;  // by flipped roots, built lazily
  LsvKlConst oc;

  LsvKlFlex(Abc_Ntk_t* ntk, Vec_Ptr_t* order, const LsvKlCut& cut, size_t workers)
      : ntk(ntk), order(order), cut(cut), workers(workers), n(cut.leaves.size()),
        m(cut.roots.size()), N(Abc_NtkObjNumMax(ntk)), nPis(Abc_NtkPiNum(ntk)),
        full((1u << (1 << m)) - 1), masks(1u << n, full), seen(masks.size()),
        orig_c(masks.size()), observed(masks.size()), point(masks.size()) {}
  ~LsvKlFlex() {
    if (aig) Aig_ManStop(aig);
  }

  std::vector<unsigned> Run() {
    BuildMiter();
    FindChain();
    SimRandom();
    SimPool();
    std::vector<Item> tasks = Tasks();
    SimBiased(1024, tasks);
    Unobserved(tasks);
    if (chain.empty()) SolveTogether(tasks);
    SimPool();
    Unobserved(tasks);
    SolveLeftovers(SolveEach(tasks));
    return masks;
  }

  void BuildMiter() {
    Abc_Ntk_t* miter = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
    Abc_Aig_t* man = (Abc_Aig_t*)miter->pManFunc;
    std::vector<Abc_Obj_t*> orig(N), forced(N);
    tfo.assign(N, 0);
    unsigned constId = Abc_ObjId(Abc_AigConst1(ntk));
    orig[constId] = forced[constId] = Abc_AigConst1(miter);
    Abc_Obj_t* obj;
    int i;
    Abc_NtkForEachPi(ntk, obj, i) orig[Abc_ObjId(obj)] = forced[Abc_ObjId(obj)] =
        Abc_NtkCreatePi(miter);
    for (int j = 0; j < m; ++j) {
      forced[cut.roots[j]] = Abc_NtkCreatePi(miter);
      tfo[cut.roots[j]] = 1;
    }
    Vec_PtrForEachEntry(Abc_Obj_t*, order, obj, i) {
      unsigned id = Abc_ObjId(obj), f0 = Abc_ObjFaninId0(obj), f1 = Abc_ObjFaninId1(obj);
      orig[id] = Abc_AigAnd(man, Abc_ObjNotCond(orig[f0], Abc_ObjFaninC0(obj)),
                            Abc_ObjNotCond(orig[f1], Abc_ObjFaninC1(obj)));
      if (tfo[id]) continue;  // a root: already a new PI
      if (tfo[f0] || tfo[f1]) {
        tfo[id] = 1;
        forced[id] = Abc_AigAnd(man, Abc_ObjNotCond(forced[f0], Abc_ObjFaninC0(obj)),
                                Abc_ObjNotCond(forced[f1], Abc_ObjFaninC1(obj)));
      } else {
        forced[id] = orig[id];
      }
    }
    Abc_Obj_t* mu = Abc_ObjNot(Abc_AigConst1(miter));
    Abc_NtkForEachPo(ntk, obj, i) {
      unsigned d = Abc_ObjFaninId0(obj);
      if (tfo[d]) mu = Abc_AigOr(man, mu, Abc_AigXor(man, orig[d], forced[d]));
    }
    for (unsigned leaf : cut.leaves) Abc_ObjAddFanin(Abc_NtkCreatePo(miter), orig[leaf]);
    Abc_ObjAddFanin(Abc_NtkCreatePo(miter), mu);
    for (unsigned root : cut.roots) Abc_ObjAddFanin(Abc_NtkCreatePo(miter), orig[root]);
    aig = Lsv_KlToAig(miter);
    Abc_NtkDelete(miter);

    val.assign(Aig_ManObjNumMax(aig), 0);
    std::vector<char> dep(Aig_ManObjNumMax(aig));
    for (int j = 0; j < m; ++j) dep[Aig_ManCi(aig, nPis + j)->Id] = 1;
    Aig_Obj_t* o;
    Aig_ManForEachNode(aig, o, i) if (dep[Aig_ObjFaninId0(o)] || dep[Aig_ObjFaninId1(o)]) {
      dep[i] = 1;
      rootTfo.push_back(i);
    }
  }

  // The PI literals that gate the roots (see Lsv_KlChain).
  void FindChain() {
    std::map<int, int> lits;
    cubes.resize(m);
    for (int j = 0; j < m; ++j)
      if (Lsv_KlGateCube(ntk, order, cut.roots[j], tfo, cubes[j])) lits.insert(cubes[j].begin(), cubes[j].end());
      else cubes[j].clear();
    chain.assign(lits.rbegin(), lits.rend());
    oc.cubes = &cubes;
  }

  uint64_t Co(int i) const {
    Aig_Obj_t* o = Aig_ManCo(aig, i);
    return val[Aig_ObjFaninId0(o)] ^ (Aig_ObjFaninC0(o) ? ~uint64_t(0) : 0);
  }

  // Simulates the PI words in val for every c and records what they show.
  void SimWord() {
    std::vector<uint64_t> leafVal(n), rootVal(m);
    auto eval = [&](Aig_Obj_t* o) {
      val[o->Id] = (val[Aig_ObjFaninId0(o)] ^ (Aig_ObjFaninC0(o) ? ~uint64_t(0) : 0)) &
                   (val[Aig_ObjFaninId1(o)] ^ (Aig_ObjFaninC1(o) ? ~uint64_t(0) : 0));
    };
    for (unsigned c = 0; c < (1u << m); ++c) {
      for (int j = 0; j < m; ++j)
        val[Aig_ManCi(aig, nPis + j)->Id] = (c >> (m - 1 - j)) & 1 ? ~uint64_t(0) : 0;
      val[Aig_ManConst1(aig)->Id] = ~uint64_t(0);
      // The rest of the network does not depend on c: simulated once per word.
      Aig_Obj_t* o;
      int i;
      if (c == 0) Aig_ManForEachNode(aig, o, i) eval(o);
      else for (int k : rootTfo) eval(Aig_ManObj(aig, k));
      if (c == 0) {
        for (int j = 0; j < n; ++j) leafVal[j] = Co(j);
        for (int j = 0; j < m; ++j) rootVal[j] = Co(n + 1 + j);
      }
      uint64_t mu = Co(n);
      for (int bit = 0; bit < 64; ++bit) {
        unsigned u = 0, r = 0;
        for (int j = 0; j < n; ++j) u = u << 1 | ((leafVal[j] >> bit) & 1);
        if (c == 0) {
          for (int j = 0; j < m; ++j) r = r << 1 | ((rootVal[j] >> bit) & 1);
          gain += !seen[u];
          seen[u] = 1;
          orig_c[u] = r;
          if (point[u].empty())
            for (int k = 0; k < nPis; ++k) point[u].push_back((val[Aig_ManCi(aig, k)->Id] >> bit) & 1);
        }
        if (((mu >> bit) & 1) && !((observed[u] >> c) & 1)) {
          observed[u] |= 1u << c, ++gain;
          if (share) {
            std::vector<char> x(nPis);
            for (int k = 0; k < nPis; ++k) x[k] = (val[Aig_ManCi(aig, k)->Id] >> bit) & 1;
            Lsv_PoolAdd(x);
          }
        }
      }
    }
  }

  // Random simulation finds most produced u, their root values, and most c
  // that a PO can observe; SAT is only asked about the rest.
  void SimRandom() {
    // Without a chain, stop once 16 words in a row find nothing new: the rest
    // goes to SAT anyway.
    for (int word = 0, last = 0; word < 256; ++word) {
      if (chain.empty() && word % 16 == 0) {
        if (word >= 32 && gain == last) break;
        last = gain;
      }
      for (int i = 0; i < nPis; ++i) val[Aig_ManCi(aig, i)->Id] = Lsv_RandWord(rng, word);
      SimWord();
    }
    // Differences at the roots only show where their gate literals hold (e.g. a
    // tiny divisor): random patterns with all but the last few of them true.
    std::vector<int> piIndex(N, -1);
    Abc_Obj_t* obj;
    int i;
    Abc_NtkForEachPi(ntk, obj, i) piIndex[Abc_ObjId(obj)] = i;
    for (int word = 0; !chain.empty() && word < 128; ++word) {
      for (int k = 0; k < nPis; ++k) {
        uint64_t r = rng();
        if (word % 3 == 1) r &= rng() & rng();
        if (word % 3 == 2) r |= rng() | rng();
        val[Aig_ManCi(aig, k)->Id] = r;
      }
      for (int k = 0; k + word % 9 < (int)chain.size(); ++k)
        val[Aig_ManCi(aig, piIndex[chain[k].first])->Id] = chain[k].second ? ~uint64_t(0) : 0;
      SimWord();
    }
  }

  // Random patterns rarely observe V in deep arithmetic. A SAT counterexample
  // does, and so do many of its neighbours, often for other u and c as well;
  // when 4 words in a row find nothing new, the rest would not either.
  void SimNear(const std::vector<char>& x, int words) {
    for (int word = 0, last = 0; word < words; ++word) {
      if (word % 4 == 0) {
        if (word && gain == last) break;
        last = gain;
      }
      std::vector<uint64_t> w = Lsv_NearWords(x, nPis, rng);
      for (int i = 0; i < nPis; ++i) val[Aig_ManCi(aig, i)->Id] = w[i];
      SimWord();
    }
  }

  // The shared counterexamples not simulated yet, 64 per word.
  unsigned poolDone = 0;
  void SimPool() {
    if (!lsvPool) return;
    unsigned end = std::min(lsvPool->n.load(), lsvPool->cap);
    while (poolDone < end) {
      for (int i = 0; i < nPis; ++i) {
        uint64_t w = 0;
        for (unsigned b = 0; b < 64; ++b)
          w |= uint64_t(lsvPool->x[(size_t)std::min(poolDone + b, end - 1) * nPis + i]) << b;
        val[Aig_ManCi(aig, i)->Id] = w;
      }
      SimWord();
      poolDone = std::min(poolDone + 64, end);
    }
  }

  bool Observed(unsigned u, unsigned c) const { return (observed[u] >> c) & 1; }

  // Drops the items simulation has decided since.
  void Unobserved(std::vector<Item>& items) const {
    std::vector<Item> rest;
    for (const auto& t : items)
      if (!Observed(t[0], t[2])) rest.push_back(t);
    items.swap(rest);
  }

  // Deep arithmetic observes some roots only on rare inputs (log2: mostly
  // ones), which a long run of biased random patterns still finds far sooner
  // than SAT: a second where SAT takes minutes. Stops once all of qs are seen.
  // Where it rarely finds anything (sqrt: never), it only costs: the budget
  // shrinks with the success rate over all cuts so far.
  bool share = false;
  void SimBiased(int words, const std::vector<Item>& qs) {
    if (qs.empty()) return;
    if (lsvPool) {
      unsigned runs = lsvPool->sbRuns++, hits = lsvPool->sbHits;
      if (runs >= 16 && 4 * hits < runs) words = std::min(words, 64 + int((long)words * 4 * hits / runs));
    }
    long g0 = gain;
    share = true;
    struct Done {
      LsvKlFlex* f;
      long g0;
      ~Done() {
        f->share = false;
        if (lsvPool && f->gain > g0) lsvPool->sbHits++;
      }
    } done{this, g0};
    for (int word = 0; word < words; ++word) {
      if (word % 64 == 0 && std::all_of(qs.begin(), qs.end(),
                                        [&](const Item& t) { return Observed(t[0], t[2]); }))
        return;
      for (int i = 0; i < nPis; ++i) {
        uint64_t r = rng();
        switch (word % 6) {  // P(1) = 1/2, 3/4, 7/8, 1/4, 15/16, 1/8
          case 1: r |= rng(); break;
          case 2: r |= rng() | rng(); break;
          case 3: r &= rng(); break;
          case 4: r |= rng() | rng() | rng(); break;
          case 5: r &= rng() & rng(); break;
        }
        val[Aig_ManCi(aig, i)->Id] = r;
      }
      SimWord();
    }
  }

  LsvKlSat* SweepFor(unsigned flip) {
    std::unique_ptr<LsvKlSat>& sw = sweeps[flip];
    if (!sw) sw.reset(new LsvKlSat(ntk, order, cut, flip));
    return sw.get();
  }

  // Settles the u simulation never produced (SAT: is u produced at all?) and
  // returns the (u, cu, c) no simulation has decided.
  std::vector<Item> Tasks() {
    std::vector<Item> tasks;
    // Glucose on the logic of the leaves and roots only: proving a u never
    // occurs can take a minute in deep arithmetic, and there it is several
    // times faster than bsat on the whole miter.
    Aig_Man_t* cone = nullptr;
    Cnf_Dat_t* cnf = nullptr;
    bmcg_sat_solver* sat = nullptr;
    for (unsigned u = 0; u < masks.size(); ++u) {
      if (!seen[u]) {
        if (!cnf) {
          cone = Aig_ManDupSimple(aig);
          Aig_ObjPatchFanin0(cone, Aig_ManCo(cone, n), Aig_ManConst0(cone));  // drop mu
          Aig_ManCleanup(cone);
          cnf = Cnf_Derive(cone, Aig_ManCoNum(cone));
          sat = bmcg_sat_solver_start();
          bmcg_sat_solver_set_nvars(sat, cnf->nVars);
          int *beg, *end, k;
          Cnf_CnfForClause(cnf, beg, end, k) if (sat && !bmcg_sat_solver_addclause(sat, beg, end - beg)) {
            bmcg_sat_solver_stop(sat);
            sat = nullptr;
          }
        }
        if (!sat) continue;  // contradictory at once: no u is produced
        auto coVar = [&](int i) { return cnf->pVarNums[Aig_ManCo(cone, i)->Id]; };
        std::vector<lit> lits(n);
        for (int j = 0; j < n; ++j) lits[j] = Abc_Var2Lit(coVar(j), !((u >> (n - 1 - j)) & 1));
        int pt = bmcg_sat_solver_solve(sat, lits.data(), n);
        if (pt == -1) continue;  // u is never produced: everything is allowed
        orig_c[u] = 0;
        for (int j = 0; j < m; ++j)
          orig_c[u] = orig_c[u] << 1 | bmcg_sat_solver_read_cex_varvalue(sat, coVar(n + 1 + j));
        point[u].assign(nPis, 0);
        for (int i = 0; i < nPis; ++i) {
          int v = cnf->pVarNums[Aig_ManCi(cone, i)->Id];
          point[u][i] = v >= 0 && bmcg_sat_solver_read_cex_varvalue(sat, v);
        }
      }
      // Patterns near a point with U = u mostly keep U = u: more chances to observe c.
      if (observed[u] != full) SimNear(point[u], 16);
      masks[u] = 1u << orig_c[u];  // the original root values are always fine
      for (unsigned c = 0; c < (1u << m); ++c)
        if (c != orig_c[u] && !Observed(u, c)) tasks.push_back({u, orig_c[u], c});
    }
    if (sat) bmcg_sat_solver_stop(sat);
    if (cnf) Cnf_DataFree(cnf);
    if (cone) Aig_ManStop(cone);
    return tasks;
  }

  // Without a chain, first try to prove all of the cut's queries in one sweep;
  // a counterexample rules one of them out, then try the rest again.
  void SolveTogether(std::vector<Item>& tasks) {
    while (tasks.size() >= 2) {
      unsigned flip = 0;
      for (const auto& t : tasks) flip |= t[1] ^ t[2];
      std::vector<char> cex;
      int bad = -1;
      int q = SweepFor(flip)->Query(tasks, cex, 2000, &bad);
      if (q < 0) break;
      if (q == 1) {
        for (const auto& t : tasks) masks[t[0]] |= 1u << t[2];
        tasks.clear();
        break;
      }
      if (cex.empty() || bad < 0) break;  // a flipped root drives a PO: no single culprit
      Lsv_PoolAdd(cex);
      SimNear(cex, 4);
      std::vector<Item> rest;
      for (size_t i = 0; i < tasks.size(); ++i)
        if ((int)i != bad && !Observed(tasks[i][0], tasks[i][2])) rest.push_back(tasks[i]);
      tasks.swap(rest);
    }
  }

  // One query with bounded budgets: 1, 0 (cex set if found) or -1.
  // Root j with gate cube G_j is unobservable where G_j fails, so there
  // c acts like c2 = c with root j back at cu. Hence if c2 is allowed, only
  // the single case G_j remains; and a counterexample of c2 found there is
  // often one of c as well (checked by simulation).
  int Solve(unsigned u, unsigned cu, unsigned c, std::vector<char>& cex) {
    LsvKlSat* sw = SweepFor(cu ^ c);
    if (chain.empty()) return sw->Query(u, cu, c, cex, 2000);
    // The cases settle most queries within a small budget. Where fixing the
    // chain PIs barely shrinks the miter they stall, and the sweep is quick
    // instead: alternate, raising the budgets.
    for (int limit : {100000, 1000000}) {
      int q = SolveCases(u, cu, c, cex, limit);
      if (q >= 0) return q;
      cex.clear();
      q = sw->Query(u, cu, c, cex, limit < 1000000 ? 200 : 2000);
      if (q >= 0) return q;
      cex.clear();
    }
    return -1;
  }

  // The chain cases with a satoko budget of limit conflicts per call.
  int SolveCases(unsigned u, unsigned cu, unsigned c, std::vector<char>& cex, int limit) {
    int q = Lsv_KlChain(ntk, order, cut, u, cu, c, chain, limit, cex, oc);
    if (q >= 0) return q;
    for (int j = 0; j < m; ++j) {
      unsigned bit = 1u << (m - 1 - j), c2 = c ^ bit;
      if (!((cu ^ c) & bit) || cubes[j].empty()) continue;
      std::vector<char> x;
      int q2 = c2 == cu ? 1 : Solve(u, cu, c2, x);
      if (q2 == 1) {
        std::vector<int> pc(N, -1);
        for (const auto& kv : cubes[j]) pc[kv.first] = kv.second;
        q = Lsv_KlCase(ntk, order, cut, u, cu, c, pc, limit, cex, oc);
        if (q >= 0) return q;
      } else if (q2 == 0 && !x.empty()) {
        Lsv_PoolAdd(x);
        SimNear(x, 1);
        if (Observed(u, c)) return 0;
      }
      break;
    }
    return -1;
  }

  // The queries are independent: spread them over the cores. Returns those
  // left undecided.
  std::vector<Item> SolveEach(const std::vector<Item>& tasks) {
    // With a chain, the c of one u share their cases (and the cached constants
    // of the original PO): one child does them all.
    std::vector<std::vector<int>> byU;
    if (!chain.empty()) {
      std::map<unsigned, std::vector<int>> g;
      for (size_t i = 0; i < tasks.size(); ++i) {
        g[tasks[i][0]].push_back(i);
        oc.cs[tasks[i][0]].push_back(tasks[i][2]);
        oc.cu[tasks[i][0]] = tasks[i][1];
      }
      for (auto& kv : g) byU.push_back(kv.second);
    }
    std::vector<int> qs = Lsv_Pool(tasks.size(), workers, [&](int i) {
      std::vector<char> cex;
      int q = Solve(tasks[i][0], tasks[i][1], tasks[i][2], cex);
      if (q == 0) Lsv_PoolAdd(cex);
      return q;
    }, byU);
    std::vector<Item> pending;
    for (size_t i = 0; i < tasks.size(); ++i) {
      if (qs[i] == 1) masks[tasks[i][0]] |= 1u << tasks[i][2];
      if (qs[i] < 0) pending.push_back(tasks[i]);
    }
    return pending;
  }

  // Unbounded, exact: a race of engines, after one more long run of biased
  // simulation. Each engine stalls on some of what is left, rarely all on the
  // same query: the sweep wins most deep UNSAT ones, cube and conquer a few
  // in div, CaDiCaL the rare-witness SAT ones in log2.
  void SolveLeftovers(const std::vector<Item>& pending) {
    SimBiased(16384, pending);
    for (const auto& it : pending) {
      unsigned u = it[0], cu = it[1], c = it[2];
      SimPool();
      if (Observed(u, c)) continue;  // a later counterexample showed it
      LsvKlSat* sw = SweepFor(cu ^ c);
      auto sweep = [&] {
        std::vector<char> x;
        int r = sw->Query(u, cu, c, x, 0);
        Lsv_PoolAdd(x);
        return r;
      };
      int q = Lsv_Race({[&] { return Lsv_KlCadicalMiter(ntk, order, cut, u, cu, c, -1, 1); },
                        [&] { return Lsv_KlCadicalMiter(ntk, order, cut, u, cu, c, 4, workers); },
                        sweep},
                       [&] {
                         SimPool();
                         return Observed(u, c);
                       });
      // Every child died (no fork, out of memory): decide it here, rather
      // than report "not allowed" without a counterexample.
      if (q < 0) q = sweep();
      if (q == 1) masks[u] |= 1u << c;
    }
  }
};

static std::vector<unsigned> Lsv_KlFlex(Abc_Ntk_t* ntk, Vec_Ptr_t* order,
                                        const LsvKlCut& cut, size_t workers) {
  return LsvKlFlex(ntk, order, cut, workers).Run();
}

// Prints the base cut and every cut obtained by adding non-output nodes of S as
// roots; their bits of c do not matter.
static void Lsv_KlPrint(const LsvKlCut& cut, const std::vector<unsigned>& masks,
                        std::vector<unsigned>& roots, size_t next, int l) {
  std::vector<unsigned> sorted = roots;
  std::sort(sorted.begin(), sorted.end());
  int m = sorted.size(), mb = cut.roots.size();
  for (int j = 0; j < m; ++j) printf("%s%u", j ? " " : "", sorted[j]);
  printf(":");
  for (unsigned leaf : cut.leaves) printf(" %u", leaf);
  printf(":");
  for (unsigned base : masks) {
    unsigned mask = 0;
    for (unsigned c = 0; c < (1u << m); ++c) {
      unsigned cb = 0;
      for (int j = 0, b = 0; j < m; ++j)
        if (b < mb && sorted[j] == cut.roots[b]) cb |= ((c >> (m - 1 - j)) & 1) << (mb - 1 - b++);
      if ((base >> cb) & 1) mask |= 1u << c;
    }
    printf(" %X", mask);
  }
  printf("\n");
  for (size_t i = next; i < cut.region.size() && static_cast<int>(roots.size()) < l; ++i) {
    unsigned v = cut.region[i];
    if (std::binary_search(cut.roots.begin(), cut.roots.end(), v)) continue;
    roots.push_back(v);
    Lsv_KlPrint(cut, masks, roots, i + 1, l);
    roots.pop_back();
  }
}

static int Lsv_CommandKlFlex(Abc_Frame_t* frame, int argc, char** argv) {
  long kl[2];
  bool ok = argc == 3;
  for (int i = 0; ok && i < 2; ++i) {
    char* end;
    errno = 0;
    kl[i] = std::strtol(argv[i + 1], &end, 10);
    ok = !errno && !*end;
  }
  if (!ok || kl[0] < 1 || kl[0] > 6 || kl[1] < 1 || kl[1] > 4) {
    Abc_Print(-2, "usage: lsv_kl_flex <k> <l> (1 <= k <= 6, 1 <= l <= 4)\n");
    return 1;
  }
  Abc_Ntk_t* ntk = Abc_FrameReadNtk(frame);
  if (!ntk || !Abc_NtkIsStrash(ntk)) {
    Abc_Print(-1, "Read a circuit and run strash first.\n");
    return 1;
  }

  LsvKlSearch s;
  s.ntk = ntk;
  s.k = kl[0];
  s.l = kl[1];
  size_t nObjs = Abc_NtkObjNumMax(ntk);
  s.inS.assign(nObjs, 0);
  s.inU.assign(nObjs, 0);
  s.mark.assign(nObjs, 0);
  s.isRoot.assign(nObjs, 0);
  std::vector<LsvCuts> cache(nObjs);
  std::vector<char> inCut(nObjs);
  Abc_Obj_t* node;
  int i;
  Abc_NtkForEachNode(ntk, node, i) {
    for (const LsvCut& cut : Lsv_EnumerateCuts(node, s.k, cache)) {
      if (cut.empty() || (cut.size() == 1 && cut[0] == Abc_ObjId(node))) continue;
      LsvKlPair p{Abc_ObjId(node), cut, {}};
      for (unsigned x : cut) inCut[x] = 1;
      std::vector<Abc_Obj_t*> stack{node};
      ++s.stamp;
      while (!stack.empty()) {
        Abc_Obj_t* t = stack.back();
        stack.pop_back();
        unsigned id = Abc_ObjId(t);
        if (inCut[id] || s.mark[id] == s.stamp || Abc_AigNodeIsConst(t)) continue;
        s.mark[id] = s.stamp;
        p.region.push_back(id);
        stack.push_back(Abc_ObjFanin0(t));
        stack.push_back(Abc_ObjFanin1(t));
      }
      for (unsigned x : cut) inCut[x] = 0;
      s.pairs.push_back(std::move(p));
    }
  }
  std::stable_sort(s.pairs.begin(), s.pairs.end(),
                   [](const LsvKlPair& a, const LsvKlPair& b) {
                     return a.region.size() > b.region.size();
                   });
  s.byLeaf.resize(nObjs);
  s.bySize.resize(s.k + 1);
  for (size_t j = 0; j < s.pairs.size(); ++j) {
    for (unsigned x : s.pairs[j].leaves) s.byLeaf[x].push_back(j);
    s.bySize[s.pairs[j].leaves.size()].push_back(j);
  }
  s.Search(0, 0);

  Vec_Ptr_t* order = Abc_NtkDfs(ntk, 1);
  // Cuts are independent: compute them in forked children, up to one per core,
  // and print in the original order.
  std::vector<std::vector<unsigned>> all(s.results.size());
  std::vector<char> have(s.results.size());
  long cores = sysconf(_SC_NPROCESSORS_ONLN);
#ifdef __linux__
  // Only the cores this process may run on (taskset, container limits).
  cpu_set_t set;
  if (sched_getaffinity(0, sizeof set, &set) == 0) cores = CPU_COUNT(&set);
#endif
  size_t workers = cores > 1 ? (size_t)cores : 1;
  // Each cut also spreads its own queries over the cores, oversubscribed up to
  // 4x in total: the OS shares them, so cores freed by finished cuts go to the
  // slow ones.
  size_t perCut = std::min(workers, std::max<size_t>(1, 4 * workers / std::max<size_t>(1, std::min(workers, s.results.size()))));
  size_t poolCap = 1 << 16, poolBytes = sizeof(LsvCexPool) + poolCap * Abc_NtkPiNum(ntk);
  void* pool = mmap(nullptr, poolBytes, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (pool != MAP_FAILED) {
    lsvPool = new (pool) LsvCexPool;
    lsvPool->n = 0, lsvPool->sbRuns = 0, lsvPool->sbHits = 0;
    lsvPool->cap = poolCap, lsvPool->nPis = Abc_NtkPiNum(ntk);
  }
  struct Job { pid_t pid; int fd; size_t cut; std::string buf; };
  std::vector<Job> jobs;
  size_t next = 0;
  auto finish = [&](Job& j) {
    size_t want = sizeof(unsigned) << s.results[j.cut].leaves.size();
    if (j.buf.size() == want) {
      all[j.cut].resize(want / sizeof(unsigned));
      memcpy(all[j.cut].data(), j.buf.data(), want);
      have[j.cut] = 1;
    }
    close(j.fd);
    waitpid(j.pid, nullptr, 0);
  };
  while (next < s.results.size() || !jobs.empty()) {
    while (next < s.results.size() && jobs.size() < workers) {
      size_t i = next++;
      int fd[2];
      pid_t pid = -1;
      if (workers > 1 && pipe(fd) == 0) {
        fflush(stdout);
        fflush(stderr);
        pid = Lsv_Fork();
        if (pid < 0) close(fd[0]), close(fd[1]);
      }
      if (pid == 0) {
        close(fd[0]);
        std::vector<unsigned> m = Lsv_KlFlex(ntk, order, s.results[i], perCut);
        Lsv_WriteAll(fd[1], m.data(), m.size() * sizeof(unsigned));
        _exit(0);
      }
      if (pid < 0) {  // no fork: do it here
        all[i] = Lsv_KlFlex(ntk, order, s.results[i], perCut);
        have[i] = 1;
        continue;
      }
      close(fd[1]);
      jobs.push_back({pid, fd[0], i, std::string()});
    }
    if (jobs.empty()) continue;
    std::vector<struct pollfd> pfds;
    for (const Job& j : jobs) pfds.push_back({j.fd, POLLIN, 0});
    if (poll(pfds.data(), pfds.size(), -1) < 0) continue;
    for (size_t k = jobs.size(); k-- > 0;) {
      if (!pfds[k].revents) continue;
      char tmp[4096];
      ssize_t r = read(jobs[k].fd, tmp, sizeof tmp);
      if (r > 0) {
        jobs[k].buf.append(tmp, r);
        continue;
      }
      finish(jobs[k]);
      jobs.erase(jobs.begin() + k);
    }
  }
  for (size_t i = 0; i < s.results.size(); ++i) {
    if (!have[i]) all[i] = Lsv_KlFlex(ntk, order, s.results[i], 1);  // a child failed
    std::vector<unsigned> roots = s.results[i].roots;
    Lsv_KlPrint(s.results[i], all[i], roots, 0, s.l);
  }
  if (lsvPool) munmap(pool, poolBytes), lsvPool = nullptr;
  Vec_PtrFree(order);
  return 0;
}
