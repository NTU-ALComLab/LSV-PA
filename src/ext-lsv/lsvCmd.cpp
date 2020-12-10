#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"

#include <iostream>
#include <vector>
#include <algorithm>
#include <string>
#include <unordered_map>

using namespace std;

static int Lsv_CommandPrintGates(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandPrintSopunate(Abc_Frame_t *pAbc, int argc, char **argv);
static int Lsv_CommandPrintPounate(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t *pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_gates", Lsv_CommandPrintGates, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPounate, 0);
}

void destroy(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintGates(Abc_Ntk_t *pNtk)
{
  Abc_Obj_t *pObj;
  int i;
  Abc_NtkForEachObj(pNtk, pObj, i)
  {
    //printf("Object Id = %d, name = %s, Data = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj), Abc_ObjData(pObj));

    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t *pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j)
    {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
  }
}

int Lsv_CommandPrintGates(Abc_Frame_t *pAbc, int argc, char **argv)
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
  Lsv_NtkPrintGates(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_gates [-h]\n");
  Abc_Print(-2, "\t        prints the gates in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters)
{
  Vec_Ptr_t *vNodes;
  Aig_Man_t *pMan;
  Aig_Obj_t *pObjNew;
  Abc_Obj_t *pObj;
  int i, nNodes, nDontCares;
  // make sure the latches follow PIs/POs
  if (fRegisters)
  {
    assert(Abc_NtkBoxNum(pNtk) == Abc_NtkLatchNum(pNtk));
    Abc_NtkForEachCi(pNtk, pObj, i) if (i < Abc_NtkPiNum(pNtk))
    {
      assert(Abc_ObjIsPi(pObj));
      if (!Abc_ObjIsPi(pObj))
        Abc_Print(1, "Abc_NtkToDar(): Temporary bug: The PI ordering is wrong!\n");
    }
    else assert(Abc_ObjIsBo(pObj));
    Abc_NtkForEachCo(pNtk, pObj, i) if (i < Abc_NtkPoNum(pNtk))
    {
      assert(Abc_ObjIsPo(pObj));
      if (!Abc_ObjIsPo(pObj))
        Abc_Print(1, "Abc_NtkToDar(): Temporary bug: The PO ordering is wrong!\n");
    }
    else assert(Abc_ObjIsBi(pObj));
    // print warning about initial values
    nDontCares = 0;
    Abc_NtkForEachLatch(pNtk, pObj, i) if (Abc_LatchIsInitDc(pObj))
    {
      Abc_LatchSetInit0(pObj);
      nDontCares++;
    }
    if (nDontCares)
    {
      Abc_Print(1, "Warning: %d registers in this network have don't-care init values.\n", nDontCares);
      Abc_Print(1, "The don't-care are assumed to be 0. The result may not verify.\n");
      Abc_Print(1, "Use command \"print_latch\" to see the init values of registers.\n");
      Abc_Print(1, "Use command \"zero\" to convert or \"init\" to change the values.\n");
    }
  }
  // create the manager
  pMan = Aig_ManStart(Abc_NtkNodeNum(pNtk) + 100);
  pMan->fCatchExor = fExors;
  pMan->nConstrs = pNtk->nConstrs;
  pMan->nBarBufs = pNtk->nBarBufs;
  pMan->pName = Extra_UtilStrsav(pNtk->pName);
  pMan->pSpec = Extra_UtilStrsav(pNtk->pSpec);
  // transfer the pointers to the basic nodes
  Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)Aig_ManConst1(pMan);
  Abc_NtkForEachCi(pNtk, pObj, i)
  {
    pObj->pCopy = (Abc_Obj_t *)Aig_ObjCreateCi(pMan);
    // initialize logic level of the CIs
    ((Aig_Obj_t *)pObj->pCopy)->Level = pObj->Level;
  }

  // complement the 1-values registers
  if (fRegisters)
  {
    Abc_NtkForEachLatch(pNtk, pObj, i) if (Abc_LatchIsInit1(pObj))
        Abc_ObjFanout0(pObj)
            ->pCopy = Abc_ObjNot(Abc_ObjFanout0(pObj)->pCopy);
  }
  // perform the conversion of the internal nodes (assumes DFS ordering)
  //    pMan->fAddStrash = 1;
  vNodes = Abc_NtkDfs(pNtk, 0);
  Vec_PtrForEachEntry(Abc_Obj_t *, vNodes, pObj, i)
  //    Abc_NtkForEachNode( pNtk, pObj, i )
  {
    pObj->pCopy = (Abc_Obj_t *)Aig_And(pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj), (Aig_Obj_t *)Abc_ObjChild1Copy(pObj));
    //        Abc_Print( 1, "%d->%d ", pObj->Id, ((Aig_Obj_t *)pObj->pCopy)->Id );
  }
  Vec_PtrFree(vNodes);
  pMan->fAddStrash = 0;
  // create the POs
  Abc_NtkForEachCo(pNtk, pObj, i)
      Aig_ObjCreateCo(pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj));
  // complement the 1-valued registers
  Aig_ManSetRegNum(pMan, Abc_NtkLatchNum(pNtk));
  if (fRegisters)
    Aig_ManForEachLiSeq(pMan, pObjNew, i) if (Abc_LatchIsInit1(Abc_ObjFanout0(Abc_NtkCo(pNtk, i))))
        pObjNew->pFanin0 = Aig_Not(pObjNew->pFanin0);
  // remove dangling nodes
  nNodes = (Abc_NtkGetChoiceNum(pNtk) == 0) ? Aig_ManCleanup(pMan) : 0;
  if (!fExors && nNodes)
    Abc_Print(1, "Abc_NtkToDar(): Unexpected %d dangling nodes when converting to AIG!\n", nNodes);
  //Aig_ManDumpVerilog( pMan, "test.v" );
  // save the number of registers
  if (fRegisters)
  {
    Aig_ManSetRegNum(pMan, Abc_NtkLatchNum(pNtk));
    pMan->vFlopNums = Vec_IntStartNatural(pMan->nRegs);
    //        pMan->vFlopNums = NULL;
    //        pMan->vOnehots = Abc_NtkConverLatchNamesIntoNumbers( pNtk );
    if (pNtk->vOnehots)
      pMan->vOnehots = (Vec_Ptr_t *)Vec_VecDupInt((Vec_Vec_t *)pNtk->vOnehots);
  }
  if (!Aig_ManCheck(pMan))
  {
    Abc_Print(1, "Abc_NtkToDar: AIG check has failed.\n");
    Aig_ManStop(pMan);
    return NULL;
  }
  return pMan;
}

bool compare(Abc_Obj_t *&a, Abc_Obj_t *&b)
{
  return (Abc_ObjId(a) < Abc_ObjId(b));
}

void print_unate(string str, vector<Abc_Obj_t *> &vec)
{
  if (!vec.empty())
  {
    cout << str << "nate inputs: ";
    cout << Abc_ObjName(vec[0]);

    for (int i = 1; i < vec.size(); ++i)
      cout << "," << Abc_ObjName(vec[i]);
    cout << '\n';
  }
}

int Lsv_CommandPrintSopunate(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);

  if (!pNtk)
  {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsSopLogic(pNtk))
  {
    Abc_Print(-1, "The network does not have SOP.\n");
    return 1;
  }

  Abc_Obj_t *pObj;
  int n;

  Abc_NtkForEachNode(pNtk, pObj, n)
  {

    vector<char> table;
    table.resize(Abc_ObjFaninNum(pObj), '-');

    if (table.empty())
      continue;

    bool flip = false;

    char *sop = (char *)Abc_ObjData(pObj);

    if (sop[table.size() + 1] == '0')
      flip = true;

    int v = 0;

    for (int i = 0; sop[i] != '\0'; ++i)
    {
      if (sop[i] == ' ')
      {
        i += 2;
        v = 0;
        continue;
      }

      if (table[v] == '-')
        table[v] = sop[i];
      else if ((table[v] == '1' && sop[i] == '0') || (table[v] == '0' && sop[i] == '1'))
        table[v] = '2';

      ++v;
    }

    if (flip)
      for (int i = 0; i < table.size(); ++i)
      {
        if (table[i] == '0')
          table[i] = '1';
        else if (table[i] == '1')
          table[i] = '0';
      }

    vector<Abc_Obj_t *> neg;
    vector<Abc_Obj_t *> pos;
    vector<Abc_Obj_t *> bi;

    int i;
    Abc_Obj_t *pFanin;
    Abc_ObjForEachFanin(pObj, pFanin, i)
    {
      if (table[i] == '0')
        neg.push_back(pFanin);
      else if (table[i] == '1')
        pos.push_back(pFanin);
      else if (table[i] == '2')
        bi.push_back(pFanin);
    }

    sort(neg.begin(), neg.end(), compare);
    sort(pos.begin(), pos.end(), compare);
    sort(bi.begin(), bi.end(), compare);

    cout << "node " << Abc_ObjName(pObj) << ":\n";

    print_unate("+u", pos);
    print_unate("-u", neg);
    print_unate("bi", bi);
  }

  return 0;
}

int Lsv_CommandPrintPounate(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);

  Abc_Obj_t *pObj;
  Abc_Obj_t *pObj_temp;
  Aig_Obj_t *Aig_pObj;
  int i;

  int c, v;

  Abc_Ntk_t *pPOcone;
  Aig_Man_t *pAig;
  Aig_Man_t *pAigNot;
  Cnf_Dat_t *pCnf;
  Cnf_Dat_t *pCnfNot;

  vector<char> unate;
  unate.resize(Abc_NtkPiNum(pNtk));

  unordered_map<int, string> id2name;
  unordered_map<string, char> name2unate;

  vector<Abc_Obj_t *> pos;
  vector<Abc_Obj_t *> neg;
  vector<Abc_Obj_t *> bi;

  Abc_NtkForEachPo(pNtk, pObj, i)
  {

    id2name.clear();
    name2unate.clear();

    pos.clear();
    neg.clear();
    bi.clear();

    for (c = 0; c < unate.size(); ++c)
      unate[c] = '-';

    pPOcone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pObj), Abc_ObjName(pObj), 0);

    if (Abc_ObjFaninC0(pObj))
      Abc_NtkPo(pPOcone, 0)->fCompl0 ^= 1;

    Abc_NtkForEachPi(pPOcone, pObj_temp, c)
    {
      id2name[Abc_ObjId(pObj_temp)] = string(Abc_ObjName(pObj_temp));
    }

    pAig = Abc_NtkToDar(pPOcone, 0, 0);
    pCnf = Cnf_Derive(pAig, 1);

    pCnfNot = Cnf_DataDup(pCnf);
    Cnf_DataLift(pCnfNot, pCnf->nVars);

    //Cnf_DataPrint(pCnf, 0);
    //Cnf_DataPrint(pCnfNot, 0);

    sat_solver *sat = (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0);

    sat_solver_setnvars(sat, 2 * pCnf->nVars);
    for (int c = 0; c < pCnfNot->nClauses; ++c)
      sat_solver_addclause(sat, pCnfNot->pClauses[c], pCnfNot->pClauses[c + 1]);

    lit temp[1];

    //F == 1
    temp[0] = toLitCond(pCnf->pVarNums[Aig_ObjId(Aig_ManCo(pAig, 0))], 0);
    sat_solver_addclause(sat, temp, temp + 1);

    //F bar == 0
    temp[0] = toLitCond(pCnfNot->pVarNums[Aig_ObjId(Aig_ManCo(pAig, 0))], 1);
    sat_solver_addclause(sat, temp, temp + 1);

    //adding alpha
    sat_solver_setnvars(sat, 2 * (pCnf->nVars) + Aig_ManCiNum(pAig));

    Aig_ManForEachCi(pAig, Aig_pObj, c)
    {

      int fvar = pCnf->pVarNums[Aig_ObjId(Aig_pObj)];
      int fbarvar = pCnfNot->pVarNums[Aig_ObjId(Aig_pObj)];
      int enable = 2 * (pCnf->nVars) + c;

      sat_solver_add_buffer_enable(sat, fvar, fbarvar, enable, 0);
    }

    lit Lits[Aig_ManCiNum(pAig) + 2];

    Aig_ManForEachCi(pAig, Aig_pObj, c)
    {

      int fvar = pCnf->pVarNums[Aig_ObjId(Aig_pObj)];
      int fbarvar = pCnfNot->pVarNums[Aig_ObjId(Aig_pObj)];

      //check positive unate
      Lits[0] = toLitCond(fvar, 1);
      Lits[1] = toLitCond(fbarvar, 0);

      for (int v = 0; v < Aig_ManCiNum(pAig); ++v)
      {
        int enable = 2 * (pCnf->nVars) + v;
        Lits[v + 2] = (v == c) ? toLitCond(enable, 1) : toLitCond(enable, 0);
      }

      int ans1 = sat_solver_solve(sat, Lits, Lits + Aig_ManCiNum(pAig) + 2, 0, 0, 0, 0);

      //check negative unate
      Lits[0] = toLitCond(fvar, 0);
      Lits[1] = toLitCond(fbarvar, 1);

      for (int v = 0; v < Aig_ManCiNum(pAig); ++v)
      {
        int enable = 2 * (pCnf->nVars) + v;
        Lits[v + 2] = (v == c) ? toLitCond(enable, 1) : toLitCond(enable, 0);
      }

      int ans2 = sat_solver_solve(sat, Lits, Lits + Aig_ManCiNum(pAig) + 2, 0, 0, 0, 0);
      //cout<<ans1<<" "<<ans2<<endl;
      
      if (ans1 == -1 && ans2 == -1)
      {
        ;
      }
      else if (ans1 == -1)
      {
        name2unate[id2name[Aig_ObjId(Aig_pObj)]] = '+';
        //cout << '+' << endl;
      }
      else if (ans2 == -1)
      {
        name2unate[id2name[Aig_ObjId(Aig_pObj)]] = '-';
        //cout << '-' << endl;
      }
      else
      {
        name2unate[id2name[Aig_ObjId(Aig_pObj)]] = 'b';
        //cout << 'b' << endl;
      }
    }

    Abc_NtkForEachPi(pNtk, pObj_temp, v)
    {
      if (name2unate.find(Abc_ObjName(pObj_temp)) == name2unate.end())
      {
        pos.push_back(pObj_temp);
        neg.push_back(pObj_temp);
      }
      else if (name2unate[Abc_ObjName(pObj_temp)] == '+')
        pos.push_back(pObj_temp);
      else if (name2unate[Abc_ObjName(pObj_temp)] == '-')
        neg.push_back(pObj_temp);
      else
        bi.push_back(pObj_temp);
    }

    sort(neg.begin(), neg.end(), compare);
    sort(pos.begin(), pos.end(), compare);
    sort(bi.begin(), bi.end(), compare);

    cout << "node " << Abc_ObjName(pObj) << ":\n";

    print_unate("+u", pos);
    print_unate("-u", neg);
    print_unate("bi", bi);
  }

  return 0;
}