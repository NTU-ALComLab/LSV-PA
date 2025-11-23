#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "lsvCmd.h"
#include <string>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "pa1", Lsv_CommandPrintMocut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMocut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "pa2_bdd", Lsv_CommandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
  Cmd_CommandAdd(pAbc, "LSV", "pa2_sat", Lsv_CommandUnateSat, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;


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


int Lsv_CommandPrintMocut(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, k = -1, l = -1;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if ( argc != globalUtilOptind + 2 )
        goto usage;
  // try{
    k = atoi(argv[globalUtilOptind]);
    l = atoi(argv[globalUtilOptind + 1]);
  
  if(k < 3 || k > 6) goto usage;
  if(l < 1 || l > 4) goto usage;

  // printf("k = %d, l = %d\n", k, l);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintMocut(pNtk, k, l);
  return 0;


usage:
  Abc_Print(-2, "usage: lsv_print_mocut [-h] <k> <l>\n");
  Abc_Print(-2, "\t        prints k-l multi-output cuts of the network\n");
  Abc_Print(-2, "\t        TODO of the lsv pa1\n");
  Abc_Print(-2, "\t-h    : print the command summary\n");
  Abc_Print(-2, "\tk     : the maximum size of the cut, 3 <= k <= 6 \n");
  Abc_Print(-2, "\tl     : the minimum number of nodes that share the cut, 1 <= l <= 4\n");
  return 1;
}

int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pNode;
  int c, k = -1, i = -1;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if ( argc != globalUtilOptind + 2 )
        goto usage;
  // try{
    k = atoi(argv[globalUtilOptind]);
    i = atoi(argv[globalUtilOptind + 1]);
  
  // if(k < 0 || k >= Abc_NtkCoNum(pNtk)){
  //   // Abc_Print(-1, ("Input k is " + std::to_string(k) + " but should be between 0 and " + std::to_string(Abc_NtkCoNum(pNtk) - 1) + ".\n").c_str());
  //   goto usage;
  // }
  // else if(i < 0 || i >= Abc_NtkCiNum(pNtk)){
  //   // Abc_Print(-1, ("Input i is " + std::to_string(i) + " but should be between 0 and " + std::to_string(Abc_NtkCiNum(pNtk) - 1) + ".\n").c_str());
  //   goto usage;
  // }
  // else 
  // printf("Output %d is unate with respect to input %d.\n", k, i);

  pNode = Abc_NtkObj(pNtk, k);
  unate_bdd(pNtk, k, i);

  return 0;

  usage:
  Abc_Print(-2, "usage: lsv_unate_bdd [-h] <k> <i>\n");
  Abc_Print(-2, "\t        Check unateness of a output w.r.t. a input of a circuit in BDD form.\n");
  Abc_Print(-2, "\t        For binate cases, provide witness input patterns.\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  Abc_Print(-2, "\tk     : the output index, 0 <= k < number of outputs\n");
  Abc_Print(-2, "\ti     : the input index, 0 <= i < number of inputs\n");
  return 1;
}

int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, k = -1, i = -1;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if ( argc != globalUtilOptind + 2 )
        goto usage;
  // try{
    k = atoi(argv[globalUtilOptind]);
    i = atoi(argv[globalUtilOptind + 1]);
  
  if(k < 0 || k >= Abc_NtkCoNum(pNtk)){
    // Abc_Print(-1, ("Input k is " + std::to_string(k) + " but should be between 0 and " + std::to_string(Abc_NtkCoNum(pNtk) - 1) + ".\n").c_str());
    goto usage;
  } /*goto usage;*/
  else if(i < 0 || i >= Abc_NtkCiNum(pNtk)){
    // Abc_Print(-1, ("Input i is " + std::to_string(i) + " but should be between 0 and " + std::to_string(Abc_NtkCiNum(pNtk) - 1) + ".\n").c_str());
    goto usage;
  } /*goto usage;*/
  else printf("Output %d is unate with respect to input %d.\n", k, i);
  return 0;

  usage:
  Abc_Print(-2, "usage: lsv_unate_sat [-h] <k> <i>\n");
  Abc_Print(-2, "\t        Check unateness of a output w.r.t. a input of a circuit in SAT form.\n");
  Abc_Print(-2, "\t        For binate cases, provide witness input patterns.\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  Abc_Print(-2, "\tk     : the output index, 0 <= k < number of outputs\n");
  Abc_Print(-2, "\ti     : the input index, 0 <= i < number of inputs\n");
  return 1;
}