#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "lsvCut.h"
#include "lsvKlFlex.h"

#include <charconv>
#include <cstdlib>
#include <cstring>
#include <sstream>

static int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandCutTt(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandKlFlex(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t *pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_kl_flex", Lsv_CommandKlFlex, 0);
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

int Lsv_CommandCutTt(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  if (argc != 2)
  {
    Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
    return 1;
  }
  if (!pNtk)
  {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk))
  {
    Abc_Print(-1, "Please run \"strash\" first.\n");
    return 1;
  }
  Lsv_NtkPrintCutTt(pNtk, atoi(argv[1]));
  return 0;
}

int Lsv_CommandCutBddSize(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  if (argc != 2)
  {
    Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
    return 1;
  }
  if (!pNtk)
  {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk))
  {
    Abc_Print(-1, "Please run \"strash\" first.\n");
    return 1;
  }
  Lsv_NtkPrintCutBddSize(pNtk, atoi(argv[1]));
  return 0;
}

// Entry point of lsv_kl_flex. pAbc holds the current network; argv is the command name, the
// leaf limit k and the root limit l. After validating them, finds the maximum KL cuts and then
// the masks of each cut. Returns 0 on success; prints a message and returns 1 if the arguments,
// the network or a SAT computation is invalid.
int Lsv_CommandKlFlex(Abc_Frame_t *pAbc, int argc, char **argv)
{
  if (argc != 3 || std::strcmp(argv[1], "-h") == 0)
  {
    Abc_Print(-2, "usage: lsv_kl_flex <k> <l>\n");
    return 1;
  }

  // limits[0] is k and limits[1] is l. Checking end makes sure the whole argument was parsed,
  // so input with trailing characters such as 3abc is rejected.
  int limits[2] = {};
  for (int i = 0; i < 2; ++i)
  {
    const char *arg = argv[i + 1];
    const char *end = arg + std::strlen(arg);
    const auto result = std::from_chars(arg, end, limits[i]);
    if (result.ec != std::errc{} || result.ptr != end || limits[i] < 0)
    {
      Abc_Print(-1, "k and l must be non-negative integers.\n");
      return 1;
    }
  }

  // pNtk is ABC's current network; both phases below use its node IDs.
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk)
  {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk))
  {
    Abc_Print(-1, "Please run \"strash\" first.\n");
    return 1;
  }
  if (!Abc_NtkIsComb(pNtk))
  {
    Abc_Print(-1, "lsv_kl_flex requires a combinational AIG.\n");
    return 1;
  }

  // Collect the line of every maximum cut in output and print only when all succeeded, so a
  // failing SAT computation never leaves partial output.
  std::ostringstream output;
  for (const KlCut &cut : Lsv_FindMaximumKlCuts(pNtk, limits[0], limits[1]))
  {
    auto masks = Lsv_ComputeFlexMasks(pNtk, cut);
    if (!masks)
    {
      Abc_Print(-1, "Could not compute KL cut flexibility.\n");
      return 1;
    }

    // One line: the IDs of V, the IDs of U, and the masks in increasing order of u.
    for (std::size_t i = 0; i < cut.roots.size(); ++i)
      output << (i ? " " : "") << cut.roots[i];
    output << ":";
    for (int leaf : cut.leaves)
      output << ' ' << leaf;
    output << ":";
    for (const auto &mask : *masks)
      output << ' ' << mask;
    output << '\n';
  }
  const std::string result = output.str();
  if (!result.empty())
    Abc_Print(1, "%s", result.c_str());
  return 0;
}
