#include <cstdio>
#include <cstdlib>
#include <vector>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "ext-lsv/pa1/lsvCut.h"

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

// ---- PA1 Ex4 --------------------------------------------------------------

static int Lsv_CutUsage(int fBdd) {
  Abc_Print(-2, "usage: %s <k>\n", fBdd ? "lsv_cut_bddsize" : "lsv_cut_tt");
  Abc_Print(-2, "\t        enumerates the k-feasible cuts of every AIG node\n");
  Abc_Print(-2, "\t        and prints %s of each cut\n",
            fBdd ? "the ROBDD size" : "the truth table in hex");
  Abc_Print(-2, "\t<k>   : the cut size, between 2 and 6\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

// Both commands share everything but the per-cut value.
static int Lsv_CutCommand(Abc_Frame_t* pAbc, int argc, char** argv, int fBdd) {
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    return Lsv_CutUsage(fBdd);
  }
  if (argc != globalUtilOptind + 1) {
    return Lsv_CutUsage(fBdd);
  }

  int k = atoi(argv[globalUtilOptind]);
  if (k < 2 || k > 6) {
    Abc_Print(-1, "The cut size <k> should be between 2 and 6.\n");
    return 1;
  }

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not a strashed AIG (run \"strash\").\n");
    return 1;
  }

  std::vector<Lsv_CutSet_t> cuts;
  Lsv_NtkEnumCuts(pNtk, k, cuts);

  // One manager for the whole run: every cut has at most k leaves and leaf j
  // always maps to variable j.
  DdManager* dd = NULL;
  if (fBdd) {
    dd = Cudd_Init(k, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  }

  Abc_Obj_t* pObj;
  int i;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    const Lsv_CutSet_t& set = cuts[Abc_ObjId(pObj)];
    for (size_t j = 0; j < set.size(); ++j) {
      const Lsv_Cut_t& cut = set[j];
      printf("%d: ", Abc_ObjId(pObj));
      for (size_t l = 0; l < cut.size(); ++l) {
        printf(l ? " %d" : "%d", cut[l]);
      }
      if (fBdd) {
        printf(": %d\n", Lsv_CutBddSize(dd, pObj, cut));
      } else {
        printf(": %llX\n", (unsigned long long)Lsv_CutTruth(pObj, cut));
      }
    }
  }

  if (dd) {
    Cudd_Quit(dd);
  }
  return 0;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  return Lsv_CutCommand(pAbc, argc, argv, 0);
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  return Lsv_CutCommand(pAbc, argc, argv, 1);
}
