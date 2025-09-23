#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

static int Lsv_PrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv);

void init_moc(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_PrintMOCuts, 0);
}

void destroy_moc(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer_moc = {init_moc, destroy_moc};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer_moc); }
} PackageRegistrationManager_moc;

int Lsv_PrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int K, L;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "klh")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if ( argc == globalUtilOptind + 2 )
  {
      K = atoi(argv[globalUtilOptind]);
      globalUtilOptind++;
      L = atoi(argv[globalUtilOptind]);
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  return 1;

usage:
  Abc_Print(-2, "usage: lsv_printmocut <k> <l> [-h]\n");
  Abc_Print(-2, "\t          prints the nodes in the network\n");
  Abc_Print(-2, "\t<k>     : maximum number of nodes in a cut (2 < k < 7)\n");
  Abc_Print(-2, "\t<l>     : minimum number of output nodes of a cut (0 < l < 5)\n");
  Abc_Print(-2, "\t-h      : print the command usage\n");
  return 1;
}