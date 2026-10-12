#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "ext-lsv/lsvCut.h"

#include <cstdlib>
#include <cstring>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandLsv(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv", Lsv_CommandLsv, 0);
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

int Lsv_CommandLsv(Abc_Frame_t* pAbc, int argc, char** argv) {
  const bool isTt =
      argc == 4 && strcmp(argv[1], "cut") == 0 && strcmp(argv[2], "tt") == 0;
  const bool isBdd = argc == 4 && strcmp(argv[1], "cut") == 0 &&
                     strcmp(argv[2], "bddsize") == 0;
  if (isTt || isBdd) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
      Abc_Print(-1, "Empty network.\n");
      return 1;
    }
    if (!Abc_NtkIsStrash(pNtk)) {
      Abc_Print(-1, "Network is not structurally hashed. Run strash first.\n");
      return 1;
    }
    char* end = nullptr;
    long k = strtol(argv[3], &end, 10);
    if (end == argv[3] || *end != '\0' || k < 1 || k > 6) {
      Abc_Print(-1, "k must be an integer from 1 to 6.\n");
      return 1;
    }
    if (isTt) {
      Lsv_PrintCutTruth(pNtk, (int)k);
    } else {
      Lsv_PrintCutBddSize(pNtk, (int)k);
    }
    return 0;
  }

  Abc_Print(-2, "usage: lsv cut tt <k>\n");
  Abc_Print(-2, "\t       prints truth tables of k-feasible cuts\n");
  Abc_Print(-2, "usage: lsv cut bddsize <k>\n");
  Abc_Print(-2, "\t       prints ROBDD sizes of k-feasible cuts\n");
  return 1;
}