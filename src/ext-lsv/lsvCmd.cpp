#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "lsvCut.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t *pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
}

void destroy(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t *pNtk)
{
  Abc_Obj_t *pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i)
  {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t *pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j)
    {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk))
    {
      printf("The SOP of this node:\n%s", (char *)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF)
  {
    switch (c)
    {
    case 'h':
      goto usage;
    default:
      goto usage;
    }
  }
  if (!pNtk)
  {
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

// Implementation of the command "bridge" function for `lsv_printmocut`
int Lsv_CommandPrintMoCut(Abc_Frame_t *pAbc, int argc, char **argv)
{
  if (argc != 3)
  {
    Abc_Print(-2, "usage: lsv_printmocut <k> <l>\n");
    return 1;
  }

  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk)
  {
    Abc_Print(-1, "Lsv_CommandPrintMoCut(): Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsStrash(pNtk))
  {
    Abc_Print(-1, "Lsv_CommandPrintMoCut(): This command only works on structurally hashed AIGs. Please run \"strash\" first.\n");
    return 1;
  }

  // Parse arguments k and l
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);

  // Validate parameters based on the assignment description
  if (k < 3 || k > 6)
  {
    Abc_Print(-1, "Lsv_CommandPrintMoCut(): k must be between 3 and 6.\n");
    return 1;
  }
  if (l < 2 || l > 4)
  {
    Abc_Print(-1, "Lsv_CommandPrintMoCut(): l must be between 2 and 4.\n");
    return 1;
  }

  // Call the main C++ logic function (defined in lsvCut.cpp)
  Lsv_NtkPrintMoCut(pNtk, k, l);

  return 0;
}