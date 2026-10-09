#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "lsvCut.h"

#include <cerrno>
#include <cstdlib>

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

// 指令介面已接好；作業的演算法請實作在 lsvCut.cpp 的 TODO。
// 這裡只處理參數與一般 ABC network 檢查，不呼叫任何內建 cut 功能。
static bool Lsv_ReadCutArguments(Abc_Frame_t* pAbc, int argc, char** argv,
                                 Abc_Ntk_t*& pNtk, int& k) {
  if (argc != 2) {
    Abc_Print(-2, "usage: %s <k> (2 <= k <= 6)\n", argv[0]);
    return false;
  }

  char* end = NULL;
  errno = 0;
  const long value = std::strtol(argv[1], &end, 10);
  if (errno != 0 || end == argv[1] || *end != '\0' || value < 2 || value > 6) {
    Abc_Print(-1, "k must be an integer from 2 to 6.\n");
    return false;
  }
  k = static_cast<int>(value);

  pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network. Use read first.\n");
    return false;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network must be a strashed AIG. Use strash first.\n");
    return false;
  }
  return true;
}

static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = NULL;
  int k = 0;
  if (!Lsv_ReadCutArguments(pAbc, argc, argv, pNtk, k))
    return 1;
  return Lsv_RunCutTruthTables(pNtk, k) ? 0 : 1;
}

static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = NULL;
  int k = 0;
  if (!Lsv_ReadCutArguments(pAbc, argc, argv, pNtk, k))
    return 1;
  return Lsv_RunCutBddSizes(pNtk, k) ? 0 : 1;
}
