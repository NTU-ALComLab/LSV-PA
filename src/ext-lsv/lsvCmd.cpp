#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <sstream>
#include <iterator>

#include "lsvCut.h"
#include "lsvInt.h"

static int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandPrintMoCut(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t *pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMoCut, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
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

static std::string CutSig(const std::vector<int> &cut)
{
  std::ostringstream oss;
  for (size_t i = 0; i < cut.size(); ++i)
  {
    if (i)
      oss << ' ';
    oss << cut[i];
  }
  return oss.str();
}

static bool IsSubset(const std::vector<int> &a, const std::vector<int> &b)
{
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size())
  {
    if (a[i] == b[j])
    {
      ++i;
      ++j;
    }
    else if (a[i] > b[j])
    {
      ++j;
    }
    else
      return false;
  }
  return i == a.size();
}

static void KeepIrredundant(std::vector<std::vector<int>> &cuts)
{
  std::sort(cuts.begin(), cuts.end());
  cuts.erase(std::unique(cuts.begin(), cuts.end()), cuts.end());
  std::vector<char> rem(cuts.size(), 0);
  for (size_t i = 0; i < cuts.size(); ++i)
  {
    for (size_t j = 0; j < cuts.size(); ++j)
    {
      if (i == j)
        continue;
      if (cuts[j].size() < cuts[i].size() && IsSubset(cuts[j], cuts[i]))
      {
        rem[i] = 1;
        break;
      }
    }
  }
  std::vector<std::vector<int>> out;
  out.reserve(cuts.size());
  for (size_t i = 0; i < cuts.size(); ++i)
    if (!rem[i])
      out.push_back(cuts[i]);
  cuts.swap(out);
}

static std::vector<std::vector<int>> MergeCuts(const std::vector<std::vector<int>> &a,
                                               const std::vector<std::vector<int>> &b,
                                               int k)
{
  std::vector<std::vector<int>> res;
  for (const auto &ca : a)
  {
    for (const auto &cb : b)
    {
      std::vector<int> u;
      std::merge(ca.begin(), ca.end(), cb.begin(), cb.end(), std::back_inserter(u));
      u.erase(std::unique(u.begin(), u.end()), u.end());
      if ((int)u.size() <= k)
        res.push_back(u);
    }
  }
  return res;
}

static void EnumerateCuts(Abc_Ntk_t *pNtk, int k, std::vector<std::vector<std::vector<int>>> &vCuts)
{
  int nObjs = Abc_NtkObjNum(pNtk);
  vCuts.assign(nObjs, {});
  Abc_Obj_t *pObj;
  int i;
  Abc_NtkForEachPi(pNtk, pObj, i)
  {
    int id = Abc_ObjId(pObj);
    vCuts[id] = {{id}};
  }
  Abc_NtkForEachNode(pNtk, pObj, i)
  {
    int id = Abc_ObjId(pObj);
    Abc_Obj_t *pF0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t *pF1 = Abc_ObjFanin1(pObj);
    int id0 = Abc_ObjId(pF0);
    int id1 = Abc_ObjId(pF1);
    const auto &c0 = vCuts[id0];
    const auto &c1 = vCuts[id1];
    std::vector<std::vector<int>> cuts;
    cuts.push_back({id});
    auto comb = MergeCuts(c0, c1, k);
    cuts.insert(cuts.end(), comb.begin(), comb.end());
    for (auto &c : cuts)
      std::sort(c.begin(), c.end());
    KeepIrredundant(cuts);
    vCuts[id] = cuts;
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