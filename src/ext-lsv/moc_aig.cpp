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
} mocPackageRegistrationManager;

int Lsv_PrintMOCuts(Abc_Frame_t* pAbc, int argc, char** argv) {
    
    return 1;
}