#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <cstdio>
#include <cstdlib>
#include <map>
#include <vector>

ABC_NAMESPACE_IMPL_START

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

static int is_subset(std::vector<int>& a, std::vector<int>& b) {
  int i = 0, j = 0;
  if ((int)a.size() > (int)b.size()) return 0;
  while (i < (int)a.size() && j < (int)b.size()) {
    if (a[i] == b[j]) {
      i++;
      j++;
    } else if (a[i] > b[j]) {
      j++;
    } else
      return 0;
  }
  return i == (int)a.size();
}

static void merge_two(std::vector<int>& a, std::vector<int>& b, std::vector<int>& out) {
  out.clear();
  int i = 0, j = 0;
  while (i < (int)a.size() && j < (int)b.size()) {
    if (a[i] < b[j])
      out.push_back(a[i++]);
    else if (a[i] > b[j])
      out.push_back(b[j++]);
    else {
      out.push_back(a[i]);
      i++;
      j++;
    }
  }
  while (i < (int)a.size()) out.push_back(a[i++]);
  while (j < (int)b.size()) out.push_back(b[j++]);
}

static void insert_cut(std::vector<std::vector<int> >& cuts, std::vector<int>& c) {
  int t;
  for (t = 0; t < (int)cuts.size(); t++) {
    if (cuts[t] == c) return;
    if (is_subset(cuts[t], c)) return;
  }
  std::vector<std::vector<int> > tmp;
  for (t = 0; t < (int)cuts.size(); t++) {
    if (!is_subset(c, cuts[t])) tmp.push_back(cuts[t]);
  }
  tmp.push_back(c);
  cuts = tmp;
}

static void collect_cuts(Abc_Ntk_t* pNtk, int k, std::vector<std::vector<std::vector<int> > >& all) {
  int nMax = Abc_NtkObjNumMax(pNtk);
  Abc_Obj_t* pObj;
  int i;
  all.clear();
  all.resize(nMax);

  Abc_NtkForEachCi(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    std::vector<int> c;
    c.push_back(id);
    all[id].push_back(c);
  }

  pObj = Abc_AigConst1(pNtk);
  if (pObj) {
    int id = Abc_ObjId(pObj);
    std::vector<int> c;
    c.push_back(id);
    all[id].push_back(c);
  }

  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    int f0 = Abc_ObjId(Abc_ObjFanin0(pObj));
    int f1 = Abc_ObjId(Abc_ObjFanin1(pObj));
    std::vector<int> triv;
    triv.push_back(id);
    insert_cut(all[id], triv);

    int a, b;
    for (a = 0; a < (int)all[f0].size(); a++) {
      for (b = 0; b < (int)all[f1].size(); b++) {
        std::vector<int> m;
        merge_two(all[f0][a], all[f1][b], m);
        if ((int)m.size() <= k) insert_cut(all[id], m);
      }
    }
  }
}

static int sim_node(Abc_Obj_t* pObj, std::map<int, int>& leaf, std::map<int, int>& memo) {
  int id = Abc_ObjId(pObj);
  if (leaf.count(id)) return leaf[id];
  if (memo.count(id)) return memo[id];
  int v0 = sim_node(Abc_ObjFanin0(pObj), leaf, memo);
  int v1 = sim_node(Abc_ObjFanin1(pObj), leaf, memo);
  if (Abc_ObjFaninC0(pObj)) v0 ^= 1;
  if (Abc_ObjFaninC1(pObj)) v1 ^= 1;
  memo[id] = v0 & v1;
  return memo[id];
}

static unsigned long long cut_tt(Abc_Obj_t* root, std::vector<int>& cut) {
  int n = (int)cut.size();
  unsigned long long tt = 0;
  unsigned long long lim = 1ULL << n;
  unsigned long long p;
  for (p = 0; p < lim; p++) {
    std::map<int, int> leaf;
    std::map<int, int> memo;
    int j;
    for (j = 0; j < n; j++) {
      int bit = (int)((p >> (n - 1 - j)) & 1ULL);
      leaf[cut[j]] = bit;
    }
    if (sim_node(root, leaf, memo)) tt |= (1ULL << p);
  }
  return tt;
}

static DdNode* make_bdd(DdManager* dd, Abc_Obj_t* pObj, std::map<int, int>& leafVar,
                        std::map<int, DdNode*>& memo) {
  int id = Abc_ObjId(pObj);
  if (leafVar.count(id)) return Cudd_bddIthVar(dd, leafVar[id]);
  if (memo.count(id)) return memo[id];

  DdNode* f0 = make_bdd(dd, Abc_ObjFanin0(pObj), leafVar, memo);
  DdNode* f1 = make_bdd(dd, Abc_ObjFanin1(pObj), leafVar, memo);
  if (Abc_ObjFaninC0(pObj)) f0 = Cudd_Not(f0);
  if (Abc_ObjFaninC1(pObj)) f1 = Cudd_Not(f1);

  DdNode* r = Cudd_bddAnd(dd, f0, f1);
  Cudd_Ref(r);
  memo[id] = r;
  return r;
}

static int cut_bdd_sz(Abc_Obj_t* root, std::vector<int>& cut) {
  int n = (int)cut.size();
  DdManager* dd = Cudd_Init(n, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Cudd_AutodynDisable(dd);

  std::map<int, int> leafVar;
  int j;
  for (j = 0; j < n; j++) leafVar[cut[j]] = j;

  std::map<int, DdNode*> memo;
  DdNode* f = make_bdd(dd, root, leafVar, memo);
  Cudd_Ref(f);
  int sz = Cudd_DagSize(f);

  std::map<int, DdNode*>::iterator it;
  for (it = memo.begin(); it != memo.end(); ++it) Cudd_RecursiveDeref(dd, it->second);
  Cudd_RecursiveDeref(dd, f);
  Cudd_Quit(dd);
  return sz;
}

static void dump_leaves(std::vector<int>& cut) {
  int i;
  for (i = 0; i < (int)cut.size(); i++) {
    if (i) printf(" ");
    printf("%d", cut[i]);
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

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (globalUtilOptind >= argc) goto usage;
  k = atoi(argv[globalUtilOptind]);
  if (k < 1) goto usage;
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "network is not strashed\n");
    return 1;
  }

  {
    std::vector<std::vector<std::vector<int> > > all;
    collect_cuts(pNtk, k, all);
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      int t;
      for (t = 0; t < (int)all[id].size(); t++) {
        printf("%d: ", id);
        dump_leaves(all[id][t]);
        printf(": %lX\n", (unsigned long)cut_tt(pObj, all[id][t]));
      }
    }
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
  Abc_Print(-2, "\t        enumerate k-feasible cuts and print truth tables\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (globalUtilOptind >= argc) goto usage;
  k = atoi(argv[globalUtilOptind]);
  if (k < 1) goto usage;
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "network is not strashed\n");
    return 1;
  }

  {
    std::vector<std::vector<std::vector<int> > > all;
    collect_cuts(pNtk, k, all);
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      int t;
      for (t = 0; t < (int)all[id].size(); t++) {
        printf("%d: ", id);
        dump_leaves(all[id][t]);
        printf(": %d\n", cut_bdd_sz(pObj, all[id][t]));
      }
    }
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
  Abc_Print(-2, "\t        enumerate k-feasible cuts and print ROBDD sizes\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

ABC_NAMESPACE_IMPL_END
