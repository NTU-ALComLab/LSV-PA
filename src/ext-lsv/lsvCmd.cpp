#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <iostream>

using namespace std;

////////////////////////////////////////////////////////////////////////
/// Command registration
////////////////////////////////////////////////////////////////////////

static int Lsv_CommandPrintMocut(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t *pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMocut, 0);
}

void destroy(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

////////////////////////////////////////////////////////////////////////
/// Data structures
////////////////////////////////////////////////////////////////////////

struct Cut
{
  vector<int> nodes; // sorted ascending
  bool operator<(const Cut &other) const
  {
    return nodes < other.nodes;
  }
};

////////////////////////////////////////////////////////////////////////
/// Helper functions
////////////////////////////////////////////////////////////////////////

// merge two cuts
static bool MergeCuts(const Cut &a, const Cut &b, Cut &result, int k)
{
  result.nodes.clear();
  set_union(a.nodes.begin(), a.nodes.end(),
            b.nodes.begin(), b.nodes.end(),
            back_inserter(result.nodes));
  return (int)result.nodes.size() <= k;
}

// check subset
static bool IsSubset(const Cut &a, const Cut &b)
{
  return includes(b.nodes.begin(), b.nodes.end(),
                  a.nodes.begin(), a.nodes.end());
}

// add cut if irredundant
static void AddCut(vector<Cut> &cuts, const Cut &newCut)
{
  // check if redundant
  for (auto &c : cuts)
  {
    if (IsSubset(c, newCut))
      return; // existing smaller cut
  }
  // remove supersets of newCut
  cuts.erase(remove_if(cuts.begin(), cuts.end(),
                       [&](Cut &c)
                       { return IsSubset(newCut, c); }),
             cuts.end());
  cuts.push_back(newCut);
}

////////////////////////////////////////////////////////////////////////
/// Core enumeration
////////////////////////////////////////////////////////////////////////

static void EnumerateCuts(Abc_Ntk_t *pNtk, int k,
                          vector<vector<Cut>> &nodeCuts)
{
  nodeCuts.resize(Abc_NtkObjNumMax(pNtk));

  Abc_Obj_t *pObj;
  int i;

  Abc_NtkForEachObj(pNtk, pObj, i)
  {
    nodeCuts[i].clear();
    // constant node
    if (Abc_AigNodeIsConst(pObj))
    {
      Cut c; // empty cut
      nodeCuts[i].push_back(c);
    }
    // primary input
    else if (Abc_ObjIsPi(pObj))
    {
      Cut c;
      c.nodes.push_back(Abc_ObjId(pObj));
      nodeCuts[i].push_back(c);
    }
    // AND node
    else if (Abc_ObjIsNode(pObj))
    {
      Abc_Obj_t *f0 = Abc_ObjFanin0(pObj);
      Abc_Obj_t *f1 = Abc_ObjFanin1(pObj);
      // printf("Node %d fanin0=%d fanin1=%d\n", pObj->Id, f0->Id, f1->Id);

      vector<Cut> &cuts0 = nodeCuts[Abc_ObjId(f0)];
      vector<Cut> &cuts1 = nodeCuts[Abc_ObjId(f1)];

      for (auto &c0 : cuts0)
      {
        for (auto &c1 : cuts1)
        {
          Cut merged;
          if (MergeCuts(c0, c1, merged, k))
          {
            AddCut(nodeCuts[i], merged);
          }
        }
      }
      Cut selfCut;
      selfCut.nodes.push_back(Abc_ObjId(pObj));
      AddCut(nodeCuts[i], selfCut);
    }
  }
}

////////////////////////////////////////////////////////////////////////
/// Command implementation
////////////////////////////////////////////////////////////////////////

int Lsv_CommandPrintMocut(Abc_Frame_t *pAbc, int argc, char **argv)
{
  if (argc != 3)
  {
    Abc_Print(-1, "Usage: lsv_printmocut <k> <l>\n");
    return 1;
  }
  int k = atoi(argv[1]);
  int l = atoi(argv[2]);
  if (k < 3 || k > 6 || l < 1 || l > 4)
  {
    Abc_Print(-1, "k must be 3~6, l must be 1~4\n");
    return 1;
  }

  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk)
  {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk))
  {
    Abc_Print(-1, "Network is not in AIG form. Run strash first.\n");
    return 1;
  }

  // enumerate cuts
  vector<vector<Cut>> nodeCuts;
  EnumerateCuts(pNtk, k, nodeCuts);

  // map: Cut -> list of output nodes
  map<Cut, vector<int>> cutMap;

  Abc_Obj_t *pObj;
  int i;
  Abc_NtkForEachObj(pNtk, pObj, i)
  {
    if (!(Abc_ObjIsPi(pObj) || Abc_ObjIsNode(pObj)))
      continue;
    for (auto &c : nodeCuts[i])
    {
      sort(c.nodes.begin(), c.nodes.end());
      cutMap[c].push_back(i);
    }
  }

  // print results
  for (auto &kv : cutMap)
  {
    if ((int)kv.second.size() >= l)
    {
      // print inputs
      for (size_t m = 0; m < kv.first.nodes.size(); m++)
      {
        printf("%d", kv.first.nodes[m]);
        if (m + 1 < kv.first.nodes.size())
          printf(" ");
      }
      printf(" : ");
      // print outputs
      sort(kv.second.begin(), kv.second.end());
      for (size_t m = 0; m < kv.second.size(); m++)
      {
        printf("%d", kv.second[m]);
        if (m + 1 < kv.second.size())
          printf(" ");
      }
      printf("\n");
    }
  }

  return 0;
}
