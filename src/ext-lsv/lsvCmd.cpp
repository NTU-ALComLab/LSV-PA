#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandLsv(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv", Lsv_CommandLsv, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

// ---------- cut enumeration (own implementation) ----------
// at most 6 leaves (Lsv_ParseK enforces k <= 6), ascending; no heap allocation
struct Cut {
  int n = 0;
  int v[6];
  Cut() = default;
  explicit Cut(int id) : n(1) { v[0] = id; }
  int size() const { return n; }
  bool empty() const { return n == 0; }
  int operator[](int i) const { return v[i]; }
  const int* begin() const { return v; }
  const int* end() const { return v + n; }
  bool operator<(const Cut& o) const {
    return std::lexicographical_compare(begin(), end(), o.begin(), o.end());
  }
  bool operator==(const Cut& o) const { return n == o.n && std::equal(begin(), end(), o.begin()); }
};
using CutList = std::vector<Cut>;

// union of two ascending cuts into m; false if > k leaves
static bool Lsv_MergeTwoCuts(const Cut& a, const Cut& b, int k, Cut& m) {
  int i = 0, j = 0, n = 0;
  while (i < a.n || j < b.n) {
    int v;
    if (j == b.n || (i < a.n && a.v[i] < b.v[j])) v = a.v[i++];
    else if (i == a.n || b.v[j] < a.v[i]) v = b.v[j++];
    else { v = a.v[i++]; j++; }
    if (n == k) return false;
    m.v[n++] = v;
  }
  m.n = n;
  return true;
}

// drop duplicates, keeping the first occurrence and the original order
static CutList Lsv_DedupKeepFirst(const CutList& c) {
  std::vector<int> idx(c.size());
  for (size_t i = 0; i < idx.size(); i++) idx[i] = (int)i;
  std::sort(idx.begin(), idx.end(), [&](int x, int y) {
    return c[x] < c[y] || (c[x] == c[y] && x < y);
  });
  std::vector<char> drop(c.size(), 0);
  for (size_t t = 1; t < idx.size(); t++)
    if (c[idx[t]] == c[idx[t - 1]]) drop[idx[t]] = 1;
  CutList out;
  out.reserve(c.size());
  for (size_t i = 0; i < c.size(); i++)
    if (!drop[i]) out.push_back(c[i]);
  return out;
}

struct Lsv_CutStore {
  Abc_Ntk_t* pNtk = nullptr;
  int k = 0;
  std::map<int, Abc_Obj_t*> id2obj;
  std::map<int, CutList> cuts;  // node id -> cuts
  std::unordered_set<int> visiting;

  void buildIdMap() {
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachObj(pNtk, pObj, i) { id2obj[Abc_ObjId(pObj)] = pObj; }
  }

  const CutList& getCuts(int id) {
    auto it = cuts.find(id);
    if (it != cuts.end()) return it->second;
    // compute on demand (DFS, avoids topological-order assumptions)
    auto pit = id2obj.find(id);
    if (pit == id2obj.end()) {
      static CutList empty;
      return empty;
    }
    Abc_Obj_t* pObj = pit->second;
    CutList res;
    if (Abc_ObjIsCi(pObj) || Abc_ObjFaninNum(pObj) == 0) {
      // PI / const : trivial cut only
      res.push_back(Cut{id});
      cuts[id] = res;
      return cuts[id];
    }
    if (visiting.count(id)) {
      // cycle should not happen in combinational AIG
      cuts[id] = res;
      return cuts[id];
    }
    visiting.insert(id);
    res.push_back(Cut{id});  // trivial cut first
    int nFanins = Abc_ObjFaninNum(pObj);
    // start from empty product
    CutList cur;
    cur.push_back(Cut());
    for (int j = 0; j < nFanins; j++) {
      Abc_Obj_t* pFan = Abc_ObjFanin(pObj, j);
      int fId = Abc_ObjId(pFan);
      const CutList& fCuts = getCuts(fId);
      CutList cand;
      for (auto& a : cur) {
        for (auto& b : fCuts) {
          Cut m;
          if (Lsv_MergeTwoCuts(a, b, k, m)) cand.push_back(m);
        }
      }
      cur = Lsv_DedupKeepFirst(cand);
    }
    // product cuts only hold ids below this node, so none equals the trivial cut
    for (auto& c : cur)
      if (!c.empty()) res.push_back(c);
    visiting.erase(id);
    cuts[id] = std::move(res);
    return cuts[id];
  }

  void enumerate(int kk) {
    k = kk;
    buildIdMap();
    Abc_Obj_t* pObj;
    int i;
    // ensure CI cuts exist
    Abc_NtkForEachCi(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      if (cuts.find(id) == cuts.end()) cuts[id] = CutList{Cut{id}};
    }
    // const1 if present
    Abc_NtkForEachObj(pNtk, pObj, i) {
      if (pObj->Type == ABC_OBJ_CONST1) {
        int id = Abc_ObjId(pObj);
        if (cuts.find(id) == cuts.end()) cuts[id] = CutList{Cut{id}};
      }
    }
    Abc_NtkForEachNode(pNtk, pObj, i) { getCuts(Abc_ObjId(pObj)); }
  }

  std::vector<int> internalIdsSorted() {
    std::vector<int> v;
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) { v.push_back(Abc_ObjId(pObj)); }
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
    return v;
  }
};

// ---------- truth table evaluation (own implementation) ----------
// Bit-parallel: each node holds a 64-bit word whose bit a is its value under
// assignment a; leaf j (sorted ascending) is bit (n-1-j) of a, so the first
// leaf is the MSB of the assignment index. Cone is evaluated once per cut.
struct Lsv_TtEval {
  Abc_Ntk_t* pNtk;
  std::vector<uint64_t> val;
  std::vector<int> stamp;  // val[id] is valid iff stamp[id] == cur
  int cur = 0;

  explicit Lsv_TtEval(Abc_Ntk_t* p)
      : pNtk(p), val(Abc_NtkObjNumMax(p), 0), stamp(Abc_NtkObjNumMax(p), 0) {}

  uint64_t rec(int id) {
    if (stamp[id] == cur) return val[id];
    Abc_Obj_t* pObj = Abc_NtkObj(pNtk, id);
    uint64_t r;
    if (pObj->Type == ABC_OBJ_CONST1) {
      r = ~0ULL;
    } else if (Abc_ObjIsCi(pObj) || Abc_ObjFaninNum(pObj) == 0) {
      r = 0;  // PI not in cut: should not happen for valid cuts
    } else {
      uint64_t v0 = rec(Abc_ObjId(Abc_ObjFanin0(pObj)));
      uint64_t v1 = rec(Abc_ObjId(Abc_ObjFanin1(pObj)));
      r = (Abc_ObjFaninC0(pObj) ? ~v0 : v0) & (Abc_ObjFaninC1(pObj) ? ~v1 : v1);
    }
    stamp[id] = cur;
    val[id] = r;
    return r;
  }

  uint64_t truth(int rootId, const Cut& cut) {
    static const uint64_t kVar[6] = {0xAAAAAAAAAAAAAAAAULL, 0xCCCCCCCCCCCCCCCCULL,
                                     0xF0F0F0F0F0F0F0F0ULL, 0xFF00FF00FF00FF00ULL,
                                     0xFFFF0000FFFF0000ULL, 0xFFFFFFFF00000000ULL};
    int n = (int)cut.size();
    ++cur;
    for (int j = 0; j < n; j++) {
      stamp[cut[j]] = cur;
      val[cut[j]] = kVar[n - 1 - j];
    }
    uint64_t t = rec(rootId);
    return n == 6 ? t : t & ((1ULL << (1 << n)) - 1);
  }
};

// ---------- BDD construction (own implementation, order by ascending ID) ----------
static DdNode* Lsv_BddBuildRec(DdManager* dd, int uId,
                               const std::unordered_set<int>& leafSet,
                               const std::unordered_map<int, int>& id2var,
                               std::map<int, Abc_Obj_t*>& id2obj,
                               std::unordered_map<int, DdNode*>& memo) {
  auto itM = memo.find(uId);
  if (itM != memo.end()) return itM->second;
  DdNode* res = nullptr;
  if (leafSet.count(uId)) {
    auto itV = id2var.find(uId);
    res = dd->vars[itV->second];
    Cudd_Ref(res);
    memo[uId] = res;
    return res;
  }
  auto itO = id2obj.find(uId);
  if (itO == id2obj.end()) {
    res = dd->one;
    Cudd_Ref(res);
    memo[uId] = res;
    return res;
  }
  Abc_Obj_t* pObj = itO->second;
  if (pObj->Type == ABC_OBJ_CONST1) {
    res = dd->one;
    Cudd_Ref(res);
    memo[uId] = res;
    return res;
  }
  int nFanins = Abc_ObjFaninNum(pObj);
  DdNode* acc = nullptr;
  for (int j = 0; j < nFanins; j++) {
    Abc_Obj_t* pFan = Abc_ObjFanin(pObj, j);
    DdNode* f = Lsv_BddBuildRec(dd, Abc_ObjId(pFan), leafSet, id2var, id2obj, memo);
    int c = (j == 0) ? Abc_ObjFaninC0(pObj) : (j == 1 ? Abc_ObjFaninC1(pObj)
                                                      : Abc_ObjFaninC(pObj, j));
    DdNode* fc = Cudd_NotCond(f, c);
    if (acc == nullptr) {
      acc = fc;
      Cudd_Ref(acc);
    } else {
      DdNode* tmp = Cudd_bddAnd(dd, acc, fc);
      if (tmp == nullptr) return nullptr;
      Cudd_Ref(tmp);
      Cudd_RecursiveDeref(dd, acc);
      acc = tmp;
    }
  }
  if (acc == nullptr) {
    acc = dd->one;
    Cudd_Ref(acc);
  }
  memo[uId] = acc;
  return acc;
}

static int Lsv_CutBddSize(DdManager* dd, int rootId, const Cut& cut,
                          const std::unordered_map<int, int>& id2var,
                          std::map<int, Abc_Obj_t*>& id2obj) {
  std::unordered_set<int> leafSet(cut.begin(), cut.end());
  std::unordered_map<int, DdNode*> memo;
  DdNode* r = Lsv_BddBuildRec(dd, rootId, leafSet, id2var, id2obj, memo);
  if (r == nullptr) return -1;
  int size = Cudd_DagSize(r);
  for (auto& kv : memo) Cudd_RecursiveDeref(dd, kv.second);
  return size;
}

static void Lsv_PrintCutLine(int nodeId, const Cut& cut, const char* valStr) {
  printf("%d: ", nodeId);
  for (size_t j = 0; j < cut.size(); j++) {
    if (j) printf(" ");
    printf("%d", cut[j]);
  }
  printf(": %s\n", valStr);
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

static int Lsv_ParseK(int argc, char** argv, int* pk) {
  if (argc != 2) return 0;
  char* end = nullptr;
  long v = strtol(argv[1], &end, 10);
  if (end == argv[1] || *end != '\0' || v < 1 || v > 6) return 0;
  *pk = (int)v;
  return 1;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG; run \"strash\" first.\n");
    return 1;
  }
  {
    int k = 0;
    if (!Lsv_ParseK(argc, argv, &k)) goto usage;
    Lsv_CutStore st;
    st.pNtk = pNtk;
    st.enumerate(k);
    Lsv_TtEval ev(pNtk);
    auto vNodes = st.internalIdsSorted();
    for (int nid : vNodes) {
      auto it = st.cuts.find(nid);
      if (it == st.cuts.end()) continue;
      for (auto& cut : it->second) {
        uint64_t t = ev.truth(nid, cut);
        char buf[32];
        snprintf(buf, sizeof(buf), "%llX", (unsigned long long)t);
        Lsv_PrintCutLine(nid, cut, buf);
      }
    }
    return 0;
  }
usage:
  Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
  Abc_Print(-2, "\t        enumerate k-feasible cuts and print truth tables\n");
  Abc_Print(-2, "\t<k>   : cut size limit (1-6)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG; run \"strash\" first.\n");
    return 1;
  }
  {
    int k = 0;
    if (!Lsv_ParseK(argc, argv, &k)) goto usage;
    Lsv_CutStore st;
    st.pNtk = pNtk;
    st.enumerate(k);
    auto vNodes = st.internalIdsSorted();
    // variable order by ascending AIG node id (smaller id closer to root)
    std::vector<int> allIds;
    for (auto& kv : st.id2obj) {
      Abc_Obj_t* p = kv.second;
      if (Abc_ObjIsCi(p) || Abc_ObjIsNode(p) || p->Type == ABC_OBJ_CONST1)
        allIds.push_back(kv.first);
    }
    std::sort(allIds.begin(), allIds.end());
    allIds.erase(std::unique(allIds.begin(), allIds.end()), allIds.end());
    std::unordered_map<int, int> id2var;
    for (size_t i = 0; i < allIds.size(); i++) id2var[allIds[i]] = (int)i;
    DdManager* dd =
        Cudd_Init((int)allIds.size(), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    if (dd == nullptr) {
      Abc_Print(-1, "Failed to init CUDD manager.\n");
      return 1;
    }
    Cudd_AutodynDisable(dd);
    for (int nid : vNodes) {
      auto it = st.cuts.find(nid);
      if (it == st.cuts.end()) continue;
      for (auto& cut : it->second) {
        int sz = Lsv_CutBddSize(dd, nid, cut, id2var, st.id2obj);
        char buf[32];
        snprintf(buf, sizeof(buf), "%d", sz);
        Lsv_PrintCutLine(nid, cut, buf);
      }
    }
    Cudd_Quit(dd);
    return 0;
  }
usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
  Abc_Print(-2, "\t        enumerate k-feasible cuts and print BDD sizes\n");
  Abc_Print(-2, "\t<k>   : cut size limit (1-6)\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

// "lsv cut tt <k>" / "lsv cut bddsize <k>": dispatch to the underscore commands
int Lsv_CommandLsv(Abc_Frame_t* pAbc, int argc, char** argv) {
  if (argc >= 3 && !strcmp(argv[1], "cut")) {
    if (!strcmp(argv[2], "tt")) return Lsv_CommandCutTt(pAbc, argc - 2, argv + 2);
    if (!strcmp(argv[2], "bddsize"))
      return Lsv_CommandCutBddSize(pAbc, argc - 2, argv + 2);
  }
  Abc_Print(-2, "usage: lsv cut tt <k>\n");
  Abc_Print(-2, "       lsv cut bddsize <k>\n");
  return 1;
}
