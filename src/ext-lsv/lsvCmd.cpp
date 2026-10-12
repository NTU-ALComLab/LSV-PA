#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "lsvCut.h"
#include <cerrno>
#include <cstdlib>
#include <cstring>

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

static int Lsv_CommandCuts(Abc_Frame_t* pAbc, int argc, char** argv,
                           bool bddSize) {
  const char* name = bddSize ? "lsv_cut_bddsize" : "lsv_cut_tt";
  if (argc != 2 || std::strcmp(argv[1], "-h") == 0) {
    Abc_Print(-2, "usage: %s <k>\n\t2 <= k <= 6; run read and strash first.\n", name);
    return 1;
  }
  char* end = nullptr;
  errno = 0;
  const long k = std::strtol(argv[1], &end, 10);
  if (errno || end == argv[1] || *end || k < 2 || k > 6) {
    Abc_Print(-1, "k must be an integer between 2 and 6.\n");
    return 1;
  }
  Abc_Ntk_t* network = Abc_FrameReadNtk(pAbc);
  if (!network) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(network)) {
    Abc_Print(-1, "The network must be a structurally hashed AIG; run strash first.\n");
    return 1;
  }
  return Lsv_PrintCuts(network, static_cast<int>(k), bddSize);
}

static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  return Lsv_CommandCuts(pAbc, argc, argv, false);
}

static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  return Lsv_CommandCuts(pAbc, argc, argv, true);
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
