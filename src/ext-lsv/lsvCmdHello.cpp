
#include <iostream>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

namespace {

static int Lsv_CommandHello(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_hello", Lsv_CommandHello, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

int Lsv_CommandHello(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Print(0, "Hello from LSV!\n");
  std::cout << "HelloWorld!" << std::endl;

  return 0;

  /*usage:
    Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
    Abc_Print(-2, "\t        prints the nodes in the network\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;*/
}
}  // namespace