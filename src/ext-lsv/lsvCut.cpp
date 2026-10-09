#include "lsvCut.h"
#include <algorithm>
#include <cinttypes>

#ifdef ABC_USE_CUDD
#include "bdd/cudd/cuddInt.h"
#endif

// merge two cuts
bool mergeCuts(const Cut &left, const Cut &right, int k, Cut &result)
{
  int i_left = 0, i_right = 0;
  result.clear();
  while (i_left < left.size() && i_right < right.size())
  {
    if (left[i_left] < right[i_right])
    {
      result.push_back(left[i_left]);
      i_left++;
    }
    else if (left[i_left] > right[i_right])
    {
      result.push_back(right[i_right]);
      i_right++;
    }
    else
    {
      result.push_back(left[i_left]);
      i_left++;
      i_right++;
    }
  }
  while (i_left < left.size())
  {
    result.push_back(left[i_left]);
    i_left++;
  }
  while (i_right < right.size())
  {
    result.push_back(right[i_right]);
    i_right++;
  }
  if (result.size() > k)
  {
    result.clear();
    return false;
  }
  return true;
}

// compute cuts for all nodes using two fanin
bool enumerateCuts(Abc_Ntk_t *pNtk, int k, CutTable &cuts)
{
  cuts.clear();
  cuts.resize(Abc_NtkObjNumMax(pNtk));
  Abc_Obj_t *pCi;
  int i;
  Abc_NtkForEachCi(pNtk, pCi, i)
  {
    int id = Abc_ObjId(pCi);
    cuts[id].push_back({id});
  }

  Abc_Obj_t *pConst1 = Abc_AigConst1(pNtk);
  int const1_id = Abc_ObjId(pConst1);
  cuts[const1_id].push_back({});

  Vec_Ptr_t *dfs_nodes = Abc_NtkDfs(pNtk, 1);
  Abc_Obj_t *pNode;

  Vec_PtrForEachEntry(Abc_Obj_t *, dfs_nodes, pNode, i)
  {
    int node_id = Abc_ObjId(pNode);
    if (!Abc_ObjIsCi(pNode) && !Abc_AigNodeIsConst(pNode))
    {
      cuts[node_id].push_back({node_id});
      Abc_Obj_t *pFanin0 = Abc_ObjFanin0(pNode);
      Abc_Obj_t *pFanin1 = Abc_ObjFanin1(pNode);
      int fanin0_id = Abc_ObjId(pFanin0);
      int fanin1_id = Abc_ObjId(pFanin1);
      for (const Cut &cut0 : cuts[fanin0_id])
      {
        for (const Cut &cut1 : cuts[fanin1_id])
        {
          Cut merged_cut;
          if (mergeCuts(cut0, cut1, k, merged_cut))
          {
            if (std::find(cuts[node_id].begin(), cuts[node_id].end(), merged_cut) == cuts[node_id].end())
            {
              cuts[node_id].push_back(merged_cut);
            }
          }
        }
      }
    }
  }
  Vec_PtrFree(dfs_nodes);
  return true;
}

// compute TT for one cut
bool evaluate(Abc_Obj_t *node, const Cut &cut, unsigned assignment)
{

  const int nodeId = Abc_ObjId(node);
  for (std::size_t j = 0; j < cut.size(); ++j)
  {
    if (cut[j] == nodeId)
      return ((assignment >> (cut.size() - 1 - j)) & 1) != 0;
    if (cut[j] > nodeId)
      break;
  }

  if (Abc_AigNodeIsConst(node))
    return true;
  if (Abc_ObjIsCi(node))
    return false;

  const bool left = ((evaluate(Abc_ObjFanin0(node), cut, assignment) != Abc_ObjFaninC0(node)) != 0);
  if (!left)
    return false;
  return ((evaluate(Abc_ObjFanin1(node), cut, assignment) != Abc_ObjFaninC1(node)) != 0);
}

// compute TT for one cut
std::uint64_t computeTruthTable(Abc_Obj_t *root, const Cut &cut)
{
  std::uint64_t truth = 0;
  const unsigned assignmentCount = 1u << cut.size();
  for (unsigned assignment = 0; assignment < assignmentCount; ++assignment)
  {
    if (evaluate(root, cut, assignment))
      truth |= std::uint64_t(1) << assignment;
  }
  return truth;
}

#ifdef ABC_USE_CUDD
DdNode *buildBdd(DdManager *manager, std::uint64_t truth, int remainingVariables, int variableIndex)
{

  if (remainingVariables == 0)
  {
    DdNode *result = Cudd_ReadOne(manager);
    if ((truth & 1) == 0)
      result = Cudd_Not(result);
    Cudd_Ref(result);
    return result;
  }

  const unsigned halfBits = 1u << (remainingVariables - 1);
  const std::uint64_t lowMask = (std::uint64_t(1) << halfBits) - 1;
  DdNode *low = buildBdd(manager, truth & lowMask, remainingVariables - 1, variableIndex + 1);
  if (!low)
    return nullptr;

  DdNode *high = buildBdd(manager, truth >> halfBits, remainingVariables - 1, variableIndex + 1);
  if (!high)
  {
    Cudd_RecursiveDeref(manager, low);
    return nullptr;
  }

  DdNode *variable = Cudd_bddIthVar(manager, variableIndex);
  DdNode *result = variable ? Cudd_bddIte(manager, variable, high, low) : nullptr;
  if (result)
    Cudd_Ref(result);
  Cudd_RecursiveDeref(manager, low);
  Cudd_RecursiveDeref(manager, high);
  return result;
}
#endif

bool Lsv_RunCutTruthTables(Abc_Ntk_t *pNtk, int k)
{
  CutTable cuts;
  if (!enumerateCuts(pNtk, k, cuts))
    return false;

  Abc_Obj_t *node;
  int i;
  Abc_NtkForEachNode(pNtk, node, i)
  {
    const int nodeId = Abc_ObjId(node);
    for (const Cut &cut : cuts[nodeId])
    {
      printf("%d:", nodeId);
      for (int leafId : cut)
        printf(" %d", leafId);
      printf(": %" PRIX64 "\n", computeTruthTable(node, cut));
    }
  }
  return true;
}

bool Lsv_RunCutBddSizes(Abc_Ntk_t *pNtk, int k)
{

#ifdef ABC_USE_CUDD
  CutTable cuts;
  if (!enumerateCuts(pNtk, k, cuts))
    return false;

  Abc_Obj_t *node;
  int i;
  Abc_NtkForEachNode(pNtk, node, i)
  {
    const int nodeId = Abc_ObjId(node);
    for (const Cut &cut : cuts[nodeId])
    {
      const std::uint64_t truth = computeTruthTable(node, cut);
      DdManager *manager = Cudd_Init(static_cast<unsigned>(cut.size()), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
      if (!manager)
        return false;
      Cudd_AutodynDisable(manager);

      DdNode *root = buildBdd(manager, truth, static_cast<int>(cut.size()), 0);
      if (!root)
      {
        Cudd_Quit(manager);
        return false;
      }

      const int size = Cudd_DagSize(root);
      printf("%d:", nodeId);
      for (int leafId : cut)
        printf(" %d", leafId);
      printf(": %d\n", size);

      Cudd_RecursiveDeref(manager, root);
      Cudd_Quit(manager);
    }
  }
  return true;
#endif
}
