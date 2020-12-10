#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "lsvCmd.h"

extern "C" {
  Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
}

static int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv);

void init_pounate(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPounate, 0);
}

void destroy_pounate(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer_pounate = {init_pounate, destroy_pounate};

struct PackageRegistrationManager_pounate {
  PackageRegistrationManager_pounate() { Abc_FrameAddInitializer(&frame_initializer_pounate); }
} lsvPackageRegistrationManager_pounate;

void Lsv_NtkPrintPoUnate(Abc_Ntk_t *pNtk)
{
  Abc_Obj_t *pObj, *pPi;
  Abc_Ntk_t *pCone;
  Aig_Man_t *pMan;
  int i, j;

  int piNum = Abc_NtkPiNum(pNtk);
  vector<bool> module_for_bool_vector_size_2(unates_size, false);

  Abc_NtkForEachPo(pNtk, pObj, i)
  {    
    vector<vector<bool>> phases(piNum, module_for_bool_vector_size_2);
    
    // Grow cone for the Po
    pCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pObj), Abc_ObjName(pObj), 1);
    pMan = Abc_NtkToDar(pCone, 0, 0);
    // CNF for F
    Cnf_Dat_t *pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    // CNF for F', more to do later
    Cnf_Dat_t *pCnf_n = Cnf_DataDup(pCnf);
    // Lift or the data var will collid with the original one
    Cnf_DataLift(pCnf_n, pCnf->nVars);

    sat_solver *pSat = (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0);
    Cnf_DataWriteIntoSolverInt(pSat, pCnf_n, 1, 0);

    int flag = pSat->size;
    sat_solver_setnvars(pSat, flag + piNum);

    // set assumptions
    int assumpNum = piNum + 3;
    int xi = piNum;
    int po = piNum + 1, po_n = piNum + 2;
    lit assump[assumpNum];

    // assign F and F', xor with fCompl0 in case PO is negative
    Abc_Obj_t *pConePo = Abc_NtkPo(pCone, 0);
    int poID = Aig_ObjId((Aig_Obj_t *)Abc_ObjFanin0(pConePo)->pCopy);
    assump[po] = toLitCond(pCnf->pVarNums[poID], 1^Abc_ObjFaninC0(pObj));
    assump[po_n] = toLitCond(pCnf_n->pVarNums[poID], 0^Abc_ObjFaninC0(pObj));
    
    // add clause
    Abc_NtkForEachPi(pCone, pPi, j)
    {
      int piID = Aig_ObjId((Aig_Obj_t *)pPi->pCopy);
      int piVar = pCnf->pVarNums[piID];
      int piVar_n = pCnf_n->pVarNums[piID];
      sat_solver_add_buffer_enable(pSat, piVar, piVar_n, flag + j, 0);
      // enable assump
      assump[j] = toLitCond(flag + j, 0);
    }
    
    Abc_NtkForEachPi(pCone, pPi, j)
    {
      // not in cone, both positive and negative unate
      if (!Abc_NodeIsTravIdCurrent(pPi))
      {
        continue;
      }

      // disable this one in order to assign value
      assump[j] = lit_neg(assump[j]);
      int piID = Aig_ObjId((Aig_Obj_t *)pPi->pCopy);

      // check negative unate: xi = 1
      assump[xi] = toLitCond(pCnf->pVarNums[piID], 1);
      if (sat_solver_simplify(pSat) == l_True &&
          sat_solver_solve(pSat, assump, assump + assumpNum, 0, 0, 0, 0) == l_True)
      {
        phases[j][positive] = true;
      }

      // check positive unate: xi' = 1
      assump[xi] = lit_neg(assump[xi]);
      if (sat_solver_simplify(pSat) == l_True &&
          sat_solver_solve(pSat, assump, assump + assumpNum, 0, 0, 0, 0) == l_True)
      {
        phases[j][negetive] = true;
      }

      assump[j] = lit_neg(assump[j]);
    }

    map<int, Abc_Obj_t *> binate;
    map<int, Abc_Obj_t *> posunate;
    map<int, Abc_Obj_t *> negunate;
    Abc_NtkForEachPi(pCone, pPi, j)
    {
      // binate
      if (phases[j][positive] && phases[j][negetive])
      {
        binate[Abc_ObjId(pPi)] = pPi;
      }
      // negetive unate
      if (!phases[j][positive])
      {
        negunate[Abc_ObjId(pPi)] = pPi;
      }
      // positive unate
      if (!phases[j][negetive])
      {
        posunate[Abc_ObjId(pPi)] = pPi;
      }
    }

    if (!(binate.empty() && posunate.empty() && negunate.empty()))
    {
      printf("node %s:\n", Abc_ObjName(pObj));
    }
    if (!posunate.empty())
    {
      printf("+unate inputs: ");
      bool flag = false;
      for (auto it : posunate)
      {
        if (flag)
        {
          printf(",%s", Abc_ObjName(it.second));
        }
        else
        {
          flag = true;
          printf("%s", Abc_ObjName(it.second));
        }
      }
      printf("\n");
    }
    if (!negunate.empty())
    {
      printf("-unate inputs: ");
      bool flag = false;
      for (auto it : negunate)
      {
        if (flag)
        {
          printf(",%s", Abc_ObjName(it.second));
        }
        else
        {
          flag = true;
          printf("%s", Abc_ObjName(it.second));
        }
      }
      printf("\n");
    }
    if (!binate.empty())
    {
      printf("binate inputs: ");
      bool flag = false;
      for (auto it : binate)
      {
        if (flag)
        {
          printf(",%s", Abc_ObjName(it.second));
        }
        else
        {
          flag = true;
          printf("%s", Abc_ObjName(it.second));
        }
      }
      printf("\n");
    }

    Aig_ManStop(pMan);
    Cnf_DataFree(pCnf);
    Cnf_DataFree(pCnf_n);
    sat_solver_delete(pSat);
    Abc_NtkDelete(pCone);
  }
}

int Lsv_CommandPrintPounate(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  abctime clk;
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
  clk = Abc_Clock();
  Lsv_NtkPrintPoUnate(pNtk);
  // Abc_PrintTime(1, "Time", Abc_Clock() - clk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
  Abc_Print(-2, "\t        print the unate information for each primary output in terms of all primary inputs\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}