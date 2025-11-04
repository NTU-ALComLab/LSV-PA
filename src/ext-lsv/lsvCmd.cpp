#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <vector>
#include <set>
#include <map>
#include <algorithm>

static int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandPrintMOCuts(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t *pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCuts, 0);
}

void destroy(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_DfsCutCompute(Abc_Obj_t *pObj, std::map<int, std::set<std::set<int>>> &mapNode2Cutset, std::map<std::set<int>, std::set<int>> &mapCut2Output, int k)
{
  int id = Abc_ObjId(pObj);
  if (mapNode2Cutset.find(id) != mapNode2Cutset.end())
    return;
  if (Abc_ObjIsPi(pObj))
  {
    mapNode2Cutset[id].insert({id});
    return;
  }
  else if (Abc_ObjIsPo(pObj))
  {
    Abc_Obj_t *pFanin;
    int i;
    Abc_ObjForEachFanin(pObj, pFanin, i)
    {
      Lsv_DfsCutCompute(pFanin, mapNode2Cutset, mapCut2Output, k);
    }
  }
  else
  {
    std::vector<int> faninIds;
    Abc_Obj_t *pFanin;
    int i;
    Abc_ObjForEachFanin(pObj, pFanin, i)
    {
      Lsv_DfsCutCompute(pFanin, mapNode2Cutset, mapCut2Output, k);
      faninIds.push_back(Abc_ObjId(pFanin));
    }
    mapNode2Cutset[id].insert({id});
    for (auto &leftCut : mapNode2Cutset[faninIds[0]])
    {
      for (auto &rightCut : mapNode2Cutset[faninIds[1]])
      {
        std::set<int> newCut = leftCut;
        newCut.insert(rightCut.begin(), rightCut.end());
        if (newCut.size() <= k)
        {
          mapNode2Cutset[id].insert(newCut);
          mapCut2Output[newCut].insert(id);
        }
      }
    }
    std::vector<std::set<int>> irredundantCuts;
    for(auto &cut1 : mapNode2Cutset[id]){
      for(auto &cut2 : mapNode2Cutset[id]){
        if(std::includes(cut1.begin(), cut1.end(), cut2.begin(), cut2.end()) && cut1 != cut2){
          irredundantCuts.push_back(cut1);
        }
      }
    }
    for(auto &cut : irredundantCuts){
      mapNode2Cutset[id].erase(cut);
      mapCut2Output.erase(cut);
    }
  }
}

void Lsv_NtkPrintMOCuts(Abc_Ntk_t *pNtk, int k, int l)
{
  std::map<int, std::set<std::set<int>>> mapNode2Cutset;
  std::map<std::set<int>, std::set<int>> mapCut2Output;

  Abc_Obj_t *pObj;
  int i;
  Abc_NtkForEachPo(pNtk, pObj, i)
  {
    Lsv_DfsCutCompute(Abc_ObjFanin0(pObj), mapNode2Cutset, mapCut2Output, k);
  }
  for(auto &it : mapCut2Output){
    if(it.second.size() >= l){
      for(auto cutNodeId : it.first){
        printf("%d ", cutNodeId);
      }
      printf(":");
      for(auto outputId : it.second){
        printf(" %d", outputId);
      }
      printf("\n");
    }
  }
}

int Lsv_CommandPrintMOCuts(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k, l;
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
  k = atoi(argv[argc - 2]);
  l = atoi(argv[argc - 1]);
  Lsv_NtkPrintMOCuts(pNtk, k, l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h] <k> <l>\n");
  Abc_Print(-2, "\t        prints the k-l multi-output cuts in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  Abc_Print(-2, "\tk : the k value of k-feasible cuts\n");
  Abc_Print(-2, "\tl : the l value of k-l multi-output cuts\n");
  return 1;
}

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