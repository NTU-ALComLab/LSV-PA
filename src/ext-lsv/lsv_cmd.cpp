
#include "ext-lsv/lsv_cmd.h"

void init(Abc_Frame_t* pAbc)
{
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", lsv::CommandPrintNodes, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", lsv::CommandPrintSOPUnate, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", lsv::CommandPrintPOUnate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;
