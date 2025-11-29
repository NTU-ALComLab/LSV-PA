#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include "sat/cnf/cnf.h"

#include <vector>
#include <set>
#include <map>
#include <algorithm>

static int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandPrintMOCuts(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandUnateBdd(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandUnateSat(Abc_Frame_t *pAbc, int argc, char **argv);

extern "C"
{
  Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
}

void init(Abc_Frame_t *pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocut", Lsv_CommandPrintMOCuts, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
}

void destroy(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkUnateBdd(Abc_Ntk_t *pNtk, int k, int i)
{
  std::map<int, int> bdd2Id;
  // Abc_NtkToBdd(pNtk);
  Abc_Obj_t *pPo = Abc_NtkPo(pNtk, k);
  Abc_Obj_t *pRoot = Abc_ObjFanin0(pPo);
  DdManager *dd = (DdManager *)pRoot->pNtk->pManFunc;
  DdNode *f = (DdNode *)pRoot->pData;
  Cudd_Ref(f);

  std::map<int, int> id2faninIndex;
  int bddIndex = -1;
  for (int j = 0; j < Abc_ObjFaninNum(pRoot); j++)
  {
    // printf("Pi %d name: %s\n", j, faninNamesArray[j]);
    // printf("Pi %d name: %d\n", j, Abc_ObjFaninId(pRoot, j));
    id2faninIndex[Abc_ObjFaninId(pRoot, j) - 1] = j;
    // printf("Pi: %d, faninIndex: %d\n", Abc_ObjFaninId(pRoot, j) - 1, j);
    if (Abc_ObjFaninId(pRoot, j) == i + 1)
    {
      bddIndex = j;
    }
  }

  if(bddIndex == -1)
  {
    printf("Independent\n");
    return;
  }

  DdNode *xi = Cudd_bddIthVar(dd, bddIndex);
  Cudd_Ref(xi);
  DdNode *not_xi = Cudd_Not(xi);
  Cudd_Ref(not_xi);

  DdNode *f0 = Cudd_Cofactor(dd, f, not_xi);
  Cudd_Ref(f0);
  DdNode *f1 = Cudd_Cofactor(dd, f, xi);
  Cudd_Ref(f1);

  if (Cudd_bddLeq(dd, f0, f1))
  {
    printf("positive unate\n");
  }
  else if (Cudd_bddLeq(dd, f1, f0))
  {
    printf("negative unate\n");
  }
  else
  {
    printf("binate\n");
    // pattern1: f0=0 and f1=1  -> diff1 = (!f0 & f1)
    DdNode *diff1 = Cudd_bddAnd(dd, Cudd_Not(f0), f1);
    Cudd_Ref(diff1);
    char *cube1 = new char[Abc_NtkPiNum(pNtk)];
    Cudd_bddPickOneCube(dd, diff1, cube1);
    // pattern2: f0=1 and f1=0  -> diff2 = (f0 & !f1)
    DdNode *diff2 = Cudd_bddAnd(dd, f0, Cudd_Not(f1));
    Cudd_Ref(diff2);
    char *cube2 = new char[Abc_NtkPiNum(pNtk)];
    Cudd_bddPickOneCube(dd, diff2, cube2);
    for (int j = 0; j < Abc_NtkPiNum(pNtk); j++)
    {
      if (j == i)
      {
        printf("-");
      }
      else
      {
        printf("%d", cube1[id2faninIndex[j]]);
      }
    }
    printf("\n");
    for (int j = 0; j < Abc_NtkPiNum(pNtk); j++)
    {
      if (j == i)
      {
        printf("-");
      }
      else
      {
        printf("%d", cube2[id2faninIndex[j]]);
      }
    }
    printf("\n");
    Cudd_RecursiveDeref(dd, diff1);
    Cudd_RecursiveDeref(dd, diff2);
  }
  Cudd_RecursiveDeref(dd, f);
  Cudd_RecursiveDeref(dd, f0);
  Cudd_RecursiveDeref(dd, f1);
  Cudd_RecursiveDeref(dd, xi);
  Cudd_RecursiveDeref(dd, not_xi);
  return;
}

int Lsv_CommandUnateBdd(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k, i;
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
  i = atoi(argv[argc - 1]);
  Lsv_NtkUnateBdd(pNtk, k, i);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_unate_bdd [-h] <k> <i>\n");
  Abc_Print(-2, "\tprints the unateness of the k-th PO in the i-th Pi\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  Abc_Print(-2, "\tk     : the k-th PO\n");
  Abc_Print(-2, "\ti     : the i-th Pi\n");
  return 1;
}

void Lsv_NtkUnateSat(Abc_Ntk_t *pNtk, int k, int i)
{
  Abc_Obj_t *pPo = Abc_NtkPo(pNtk, k);
  int isComplemented = Abc_ObjFaninC0(pPo);
  // printf("isComplemented: %d\n", isComplemented);
  Abc_Obj_t *pRoot = Abc_ObjFanin0(pPo);
  Abc_Ntk_t *pCone = Abc_NtkCreateCone(pNtk, pRoot, Abc_ObjName(pPo), 1);
  Aig_Man_t *pAig = Abc_NtkToDar(pCone, 0, 0);
  sat_solver *pSat = sat_solver_new();
  Cnf_Dat_t *pCnfA = Cnf_Derive(pAig, 1);
  pSat = (sat_solver *)Cnf_DataWriteIntoSolverInt(pSat, pCnfA, 1, 0);
  Cnf_Dat_t *pCnfB = Cnf_Derive(pAig, 1);
  Cnf_DataLift(pCnfB, pCnfA->nVars);
  pSat = (sat_solver *)Cnf_DataWriteIntoSolverInt(pSat, pCnfB, 2, 0);
  int idx;
  int xA = -1, xB = -1, yA = -1, yB = -1;
  Aig_Obj_t *pObj;
  Aig_ManForEachCi(pAig, pObj, idx)
  {
    int vA = pCnfA->pVarNums[pObj->Id];
    int vB = pCnfB->pVarNums[pObj->Id];
    if (idx == i)
    {
      xA = vA;
      xB = vB;
    }
    else
    {
      // other Pis
      lit clause1[2] = {toLitCond(vA, 0), toLitCond(vB, 1)};
      sat_solver_addclause(pSat, clause1, clause1 + 2);
      lit clause2[2] = {toLitCond(vA, 1), toLitCond(vB, 0)};
      sat_solver_addclause(pSat, clause2, clause2 + 2);
    }
  }
  Aig_Obj_t *pCo = Aig_ManCo(pAig, 0);
  yA = pCnfA->pVarNums[pCo->Id];
  yB = pCnfB->pVarNums[pCo->Id];
  lit assumpPos[4] = {toLitCond(xA, 1), toLitCond(xB, 0), toLitCond(yA, isComplemented ? 1 : 0), toLitCond(yB, isComplemented ? 0 : 1)};
  lit assumpNeg[4] = {toLitCond(xA, 1), toLitCond(xB, 0), toLitCond(yA, isComplemented ? 0 : 1), toLitCond(yB, isComplemented ? 1 : 0)};
  int pos_sat = sat_solver_solve(pSat, assumpPos, assumpPos + 4, 0, 0, 0, 0);
  int neg_sat = sat_solver_solve(pSat, assumpNeg, assumpNeg + 4, 0, 0, 0, 0);
  if (pos_sat == l_Undef || neg_sat == l_Undef)
  {
    printf("undefined\n");
  }
  else if (pos_sat == l_False && neg_sat == l_False)
  {
    printf("independent\n");
  }
  else if (pos_sat == l_False && neg_sat == l_True)
  {
    printf("positive unate\n");
  }
  else if (pos_sat == l_True && neg_sat == l_False)
  {
    printf("negative unate\n");
  }
  else
  {
    printf("binate\n");
    sat_solver_solve(pSat, assumpNeg, assumpNeg + 4, 0, 0, 0, 0);
    Aig_ManForEachCi(pAig, pObj, idx)
    {
      if (idx == i)
      {
        printf("-");
      }
      else
      {
        int vA = pCnfA->pVarNums[pObj->Id];
        int val = sat_solver_var_value(pSat, vA);
        printf("%d", val);
      }
    }
    printf("\n");
    sat_solver_solve(pSat, assumpPos, assumpPos + 4, 0, 0, 0, 0);
    Aig_ManForEachCi(pAig, pObj, idx)
    {
      if (idx == i)
      {
        printf("-");
      }
      else
      {
        int vB = pCnfB->pVarNums[pObj->Id];
        int val = sat_solver_var_value(pSat, vB);
        printf("%d", val);
      }
    }
    printf("\n");
  }
}

int Lsv_CommandUnateSat(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k, i;
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
  i = atoi(argv[argc - 1]);
  Lsv_NtkUnateSat(pNtk, k, i);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_unate_sat [-h] <k> <i>\n");
  Abc_Print(-2, "\tprints the unateness of the k-th PO in the i-th Pi\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  Abc_Print(-2, "\tk     : the k-th PO\n");
  Abc_Print(-2, "\ti     : the i-th Pi\n");
  return 1;
}

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
    for (auto &cut1 : mapNode2Cutset[id])
    {
      for (auto &cut2 : mapNode2Cutset[id])
      {
        if (std::includes(cut1.begin(), cut1.end(), cut2.begin(), cut2.end()) && cut1 != cut2)
        {
          irredundantCuts.push_back(cut1);
        }
      }
    }
    for (auto &cut : irredundantCuts)
    {
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
  for (auto &it : mapCut2Output)
  {
    if (it.second.size() >= l)
    {
      for (auto cutNodeId : it.first)
      {
        printf("%d ", cutNodeId);
      }
      printf(":");
      for (auto outputId : it.second)
      {
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