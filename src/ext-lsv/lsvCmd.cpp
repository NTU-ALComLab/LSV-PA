#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#endif

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <vector>

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

struct Lsv_Cut {
  std::vector<int> leaves;
  uint64_t tt;
};

static int Lsv_CutBit(uint64_t tt, int idx) { return (int)((tt >> idx) & 1ULL); }

// Cut leaf order is left-to-right MSB→LSB in the assignment index (PDF encoding).
static int Lsv_LeafBitFromAssign(int assignment, int nLeaves, int leafPos) {
  return (assignment >> (nLeaves - 1 - leafPos)) & 1;
}

static uint64_t Lsv_EvalCutTt(const Lsv_Cut& cut, int nLeaves, const int* leaves,
                             int assignment) {
  int nLocal = (int)cut.leaves.size();
  int local = 0;
  for (int i = 0; i < nLocal; i++) {
    int lit = cut.leaves[i];
    int pos = -1;
    for (int j = 0; j < nLeaves; j++) {
      if (leaves[j] == lit) {
        pos = j;
        break;
      }
    }
    if (Lsv_LeafBitFromAssign(assignment, nLeaves, pos))
      local |= (1 << (nLocal - 1 - i));
  }
  return (uint64_t)Lsv_CutBit(cut.tt, local);
}

static bool Lsv_MergeLeaves(const Lsv_Cut& a, const Lsv_Cut& b, int k,
                            std::vector<int>& out) {
  out.clear();
  size_t i = 0, j = 0;
  while (i < a.leaves.size() && j < b.leaves.size()) {
    if (a.leaves[i] == b.leaves[j]) {
      out.push_back(a.leaves[i]);
      i++;
      j++;
    } else if (a.leaves[i] < b.leaves[j]) {
      out.push_back(a.leaves[i++]);
    } else {
      out.push_back(b.leaves[j++]);
    }
    if ((int)out.size() > k) return false;
  }
  while (i < a.leaves.size()) {
    out.push_back(a.leaves[i++]);
    if ((int)out.size() > k) return false;
  }
  while (j < b.leaves.size()) {
    out.push_back(b.leaves[j++]);
    if ((int)out.size() > k) return false;
  }
  return true;
}

static uint64_t Lsv_MergeTt(const Lsv_Cut& c0, const Lsv_Cut& c1, int fCompl0,
                           int fCompl1, const std::vector<int>& leaves) {
  int n = (int)leaves.size();
  uint64_t tt = 0;
  int nAssign = 1 << n;
  for (int m = 0; m < nAssign; m++) {
    int v0 = (int)Lsv_EvalCutTt(c0, n, leaves.data(), m);
    int v1 = (int)Lsv_EvalCutTt(c1, n, leaves.data(), m);
    if (fCompl0) v0 ^= 1;
    if (fCompl1) v1 ^= 1;
    if (v0 & v1) tt |= (1ULL << m);
  }
  return tt;
}

// Dominated cuts (strict supersets of another cut of the same node) are not
// reported (TA clarification, LSV-PA issue #983). Returns false if `leaves` is
// dominated by (or equal to) an existing cut; otherwise erases the existing cuts
// that `leaves` dominates.
static bool Lsv_AddIfUndominated(std::vector<Lsv_Cut>& cuts,
                                 const std::vector<int>& leaves) {
  for (size_t i = 0; i < cuts.size(); i++) {
    if (std::includes(leaves.begin(), leaves.end(), cuts[i].leaves.begin(),
                      cuts[i].leaves.end()))
      return false;
  }
  size_t w = 0;
  for (size_t i = 0; i < cuts.size(); i++) {
    if (!std::includes(cuts[i].leaves.begin(), cuts[i].leaves.end(),
                       leaves.begin(), leaves.end()))
      cuts[w++] = cuts[i];
  }
  cuts.resize(w);
  return true;
}

static void Lsv_EnumerateCuts(Abc_Ntk_t* pNtk, int k,
                              std::vector<std::vector<Lsv_Cut> >& cuts) {
  int nObjs = Abc_NtkObjNumMax(pNtk);
  cuts.assign(nObjs, std::vector<Lsv_Cut>());

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachCi(pNtk, pObj, i) {
    Lsv_Cut c;
    c.leaves.push_back(Abc_ObjId(pObj));
    c.tt = 0x2;
    cuts[Abc_ObjId(pObj)].push_back(c);
  }

  Abc_NtkForEachNode(pNtk, pObj, i) {
    int id = Abc_ObjId(pObj);
    Lsv_Cut triv;
    triv.leaves.push_back(id);
    triv.tt = 0x2;
    cuts[id].push_back(triv);

    Abc_Obj_t* pF0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* pF1 = Abc_ObjFanin1(pObj);
    int c0 = Abc_ObjFaninC0(pObj);
    int c1 = Abc_ObjFaninC1(pObj);
    const std::vector<Lsv_Cut>& cuts0 = cuts[Abc_ObjId(pF0)];
    const std::vector<Lsv_Cut>& cuts1 = cuts[Abc_ObjId(pF1)];

    for (size_t a = 0; a < cuts0.size(); a++) {
      for (size_t b = 0; b < cuts1.size(); b++) {
        std::vector<int> leaves;
        if (!Lsv_MergeLeaves(cuts0[a], cuts1[b], k, leaves)) continue;
        if (!Lsv_AddIfUndominated(cuts[id], leaves)) continue;
        Lsv_Cut cut;
        cut.leaves = leaves;
        cut.tt = Lsv_MergeTt(cuts0[a], cuts1[b], c0, c1, leaves);
        cuts[id].push_back(cut);
      }
    }
  }
}

static void Lsv_PrintCutLeaves(const std::vector<int>& leaves) {
  for (size_t i = 0; i < leaves.size(); i++) {
    if (i) printf(" ");
    printf("%d", leaves[i]);
  }
}

static void Lsv_PrintTtHex(uint64_t tt) {
  printf("%lX", (unsigned long)tt);
}

#ifdef ABC_USE_CUDD
// TT: leftmost leaf = MSB of assignment. CUDD var 0 = leftmost leaf (smallest ID)
// so smaller IDs are closer to the ROBDD root.
static DdNode* Lsv_TtToBddAt(DdManager* dd, uint64_t tt, int cuddVar, int nvars) {
  if (nvars == 0)
    return (tt & 1) ? Cudd_ReadOne(dd) : Cudd_ReadLogicZero(dd);

  uint64_t lo = 0, hi = 0;
  int msb = 1 << (nvars - 1);
  for (int m = 0; m < (1 << nvars); m++) {
    int rest = m & (msb - 1);
    if (m & msb) {
      if (Lsv_CutBit(tt, m)) hi |= (1ULL << rest);
    } else {
      if (Lsv_CutBit(tt, m)) lo |= (1ULL << rest);
    }
  }
  DdNode* e = Lsv_TtToBddAt(dd, lo, cuddVar + 1, nvars - 1);
  Cudd_Ref(e);
  DdNode* t = Lsv_TtToBddAt(dd, hi, cuddVar + 1, nvars - 1);
  Cudd_Ref(t);
  DdNode* r = Cudd_bddIte(dd, Cudd_bddIthVar(dd, cuddVar), t, e);
  Cudd_Ref(r);
  Cudd_RecursiveDeref(dd, e);
  Cudd_RecursiveDeref(dd, t);
  Cudd_Deref(r);
  return r;
}
#endif

static int Lsv_ParseK(int argc, char** argv, int* pk) {
  if (argc != 2) return 0;
  char* end = NULL;
  long k = strtol(argv[1], &end, 10);
  if (end == argv[1] || *end != '\0' || k < 2 || k > 6) return 0;
  *pk = (int)k;
  return 1;
}

static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int k;
  if (argc == 2 && (!strcmp(argv[1], "-h") || !strcmp(argv[1], "--help")))
    goto usage;
  if (!Lsv_ParseK(argc, argv, &k)) goto usage;
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not an AIG. Run \"strash\" first.\n");
    return 1;
  }

  {
    std::vector<std::vector<Lsv_Cut> > cuts;
    Lsv_EnumerateCuts(pNtk, k, cuts);
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      for (size_t c = 0; c < cuts[id].size(); c++) {
        printf("%d: ", id);
        Lsv_PrintCutLeaves(cuts[id][c].leaves);
        printf(": ");
        Lsv_PrintTtHex(cuts[id][c].tt);
        printf("\n");
      }
    }
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
  Abc_Print(-2,
            "\t        enumerate k-feasible cuts and print truth tables (k=2..6)\n");
  return 1;
}

static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int k;
  if (argc == 2 && (!strcmp(argv[1], "-h") || !strcmp(argv[1], "--help")))
    goto usage;
  if (!Lsv_ParseK(argc, argv, &k)) goto usage;
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Network is not an AIG. Run \"strash\" first.\n");
    return 1;
  }

#ifndef ABC_USE_CUDD
  Abc_Print(-1, "CUDD is not enabled in this ABC build.\n");
  return 1;
#else
  {
    std::vector<std::vector<Lsv_Cut> > cuts;
    Lsv_EnumerateCuts(pNtk, k, cuts);
    DdManager* dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      int id = Abc_ObjId(pObj);
      for (size_t c = 0; c < cuts[id].size(); c++) {
        int n = (int)cuts[id][c].leaves.size();
        DdNode* b = Lsv_TtToBddAt(dd, cuts[id][c].tt, 0, n);
        Cudd_Ref(b);
        int sz = Cudd_DagSize(b);
        Cudd_RecursiveDeref(dd, b);
        printf("%d: ", id);
        Lsv_PrintCutLeaves(cuts[id][c].leaves);
        printf(": %d\n", sz);
      }
    }
    Cudd_Quit(dd);
  }
  return 0;
#endif

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
  Abc_Print(-2,
            "\t        enumerate k-feasible cuts and print ROBDD sizes (k=2..6)\n");
  return 1;
}
