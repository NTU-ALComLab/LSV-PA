#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "lsvCut.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t* frame, int argc, char** argv);

// Register commands at ABC startup; the final argument 0 marks them as read-only.
// lsvCut.cpp implements both Q4 commands; lsv_print_nodes retains node inspection.
void init(Abc_Frame_t* frame) {
  Cmd_CommandAdd(frame, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(frame, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(frame, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
}

void destroy(Abc_Frame_t* frame) {}

// Use the existing module initialization mechanism to register init and destroy with ABC.
Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() {
    Abc_FrameAddInitializer(&frame_initializer);
  }
} lsvPackageRegistrationManager;

// Print each internal node's ID, name, and fanins, plus its function for SOP networks.
void Lsv_NtkPrintNodes(Abc_Ntk_t* network) {
  Abc_Obj_t* node;
  int node_index;
  Abc_NtkForEachNode(network, node, node_index) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(node), Abc_ObjName(node));

    Abc_Obj_t* fanin;
    int fanin_index;
    Abc_ObjForEachFanin(node, fanin, fanin_index) {
      printf("  Fanin-%d: Id = %d, name = %s\n", fanin_index, Abc_ObjId(fanin),
             Abc_ObjName(fanin));
    }
    if (Abc_NtkHasSop(network)) {
      printf("The SOP of this node:\n%s", static_cast<char*>(node->pData));
    }
  }
}

static void PrintNodesUsage() {
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
}

// Preserve the original arguments and error messages; inspect nodes after validation.
int Lsv_CommandPrintNodes(Abc_Frame_t* frame, int argc, char** argv) {
  Abc_Ntk_t* network = Abc_FrameReadNtk(frame);
  Extra_UtilGetoptReset();
  const int option = Extra_UtilGetopt(argc, argv, "h");
  if (option != EOF) {
    PrintNodesUsage();
    return 1;
  }
  if (!network) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  Lsv_NtkPrintNodes(network);
  return 0;
}
