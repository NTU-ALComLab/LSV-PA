#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

// STL related
#include <vector>
#include <set>
#include <map>

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandPrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandUnateBDD(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandUnateSAT(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCuts, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBDD, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSAT, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;
