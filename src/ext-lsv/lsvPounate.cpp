#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "misc/vec/vec.h"
#include <vector>
#include <string>
#include <algorithm>
using namespace std;

static int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv);

void lsv_print_pounate_init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPounate, 0);
}

void lsv_print_pounate_destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t lsv_print_pounate_initializer = {lsv_print_pounate_init, lsv_print_pounate_destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&lsv_print_pounate_initializer); }
} lsv_print_pounate_PackageRegistrationManager;

int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv) {
  //printf("Lsv_CommandPrintPounate\n");
  
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
  Lsv_NtkPrintPounate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
  Abc_Print(-2, "\t        print the unate information for each primary output in terms of all primary inputs\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

void Lsv_NtkPrintPounate(Abc_Ntk_t* pNtk) {
}
