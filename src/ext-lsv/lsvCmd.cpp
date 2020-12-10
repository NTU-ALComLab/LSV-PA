#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
// #include "base/abc/abcDar.h"
#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <vector>
#include <ctime>
using namespace std;

extern "C" Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
extern "C" Cnf_Dat_t *Cnf_Derive(Aig_Man_t *pAig, int nOutputs);

static int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t *pAbc)
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintNodes, 0);
}

void destroy(Abc_Frame_t *pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t *pNtk, int argc, char **argv)
{
  const clock_t begin_time = clock();
  // cout << "PI #: " << Abc_NtkPiNum(pNtk) << endl;
  // cout << "PO #: " << Abc_NtkPoNum(pNtk) << endl;
  map<string, size_t> globalNameToId;
  map<size_t, string> globalIdToName;
  Abc_Obj_t *pObj;
  int i;
  size_t cntVar = 0;
  Abc_NtkForEachPi(pNtk, pObj, i)
  {
    globalNameToId[Abc_ObjName(pObj)] = pObj->Id;
    globalIdToName[pObj->Id] = Abc_ObjName(pObj);
  }

  // 2. For each PO
  Abc_NtkForEachPo(pNtk, pObj, i)
  {
    // 2-1: Extract cone for each PO
    Abc_Ntk_t *pNtkOn1 = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pObj), Abc_ObjName(pObj), 0);
    // record name of used pi
    size_t j;
    Abc_Obj_t *pObjOut;
    map<string, size_t> localNameToId;
    map<size_t, string> localIdToName;
    Abc_NtkForEachPi(pNtkOn1, pObjOut, j)
    {
      localNameToId[Abc_ObjName(pObjOut)] = pObjOut->Id;
      localIdToName[pObjOut->Id] = Abc_ObjName(pObjOut);
    }

    // 2-2: Convert each ckt to aig
    Aig_Man_t *pMan = Abc_NtkToDar(pNtkOn1, 0, 0);
    // Complement each PO if need

    bool isComplment = Abc_ObjFaninC0(pObj);
    if (isComplment)
    {
      Aig_ManFlipFirstPo(pMan);
    }
    //////////////////////////////////////////////////////////////
    cout << "node " << Abc_ObjName(pObj) << ":" << endl;

    // 2-3: Convert each aig to CNF
    Cnf_Dat_t *pCnfOn = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    Cnf_Dat_t *pCnfOff = Cnf_DataDup(pCnfOn);
    Cnf_DataLift(pCnfOff, pCnfOn->nVars);

    // 2-4: initialize SAT solver
    // initialize the solver
    sat_solver *pSat = sat_solver_new();
    sat_solver_setnvars(pSat, pCnfOn->nVars + pCnfOff->nVars + Aig_ManCiNum(pMan));
    // add clauses of CnfOn
    for (size_t j = 0; j < pCnfOn->nClauses; j++)
    {
      if (!sat_solver_addclause(pSat, pCnfOn->pClauses[j], pCnfOn->pClauses[j + 1]))
      {
        Cnf_DataFree(pCnfOn);
        sat_solver_delete(pSat);
        return;
      }
    }
    // add clauses of Cnfoff
    for (size_t j = 0; j < pCnfOff->nClauses; j++)
    {
      if (!sat_solver_addclause(pSat, pCnfOff->pClauses[j], pCnfOff->pClauses[j + 1]))
      {
        Cnf_DataFree(pCnfOff);
        sat_solver_delete(pSat);
        return;
      }
    }

    // 2-5: manipulate SAT solver
    // Establish equivalence of two variable
    size_t ciNum = Aig_ManCiNum(pMan);
    // cout << "ciNum: " << ciNum << endl;
    for (size_t j = 0; j < ciNum; j++)
    {
      Aig_Obj_t *aigObj = Aig_ManCi(pMan, j);
      int xOnI = pCnfOn->pVarNums[aigObj->Id];
      int xOffI = pCnfOff->pVarNums[aigObj->Id];
      // cout << "establish equivalence among (" << xOnI << ", " << xOffI << ") with enable: " << (pCnfOn->nVars+pCnfOff->nVars+j) << endl;
      sat_solver_add_buffer_enable(pSat, xOnI, xOffI, (pCnfOn->nVars + pCnfOff->nVars + j), 0);
    }
    cntVar += pCnfOn->nVars;

    // Perform SAT solver
    int *vars = new int[ciNum + 4];
    size_t outId = Aig_ManCo(pMan, 0)->Id;
    map<size_t, bool> idToIsPosUnate;
    map<size_t, bool> idToIsNegUnate;
    for (size_t j = 0; j < ciNum; j++)
    {
      for (size_t k = 0; k < ciNum; k++)
      {
        int curVar = pCnfOn->nVars + pCnfOff->nVars + k;
        if (k != j)
          vars[k] = toLitCond(curVar, 0); // check this clause
        else
        {
          vars[k] = toLitCond(curVar, 1);
          Aig_Obj_t *aigObj = Aig_ManCi(pMan, k);
          int xOnI = pCnfOn->pVarNums[aigObj->Id];
          int xOffI = pCnfOff->pVarNums[aigObj->Id];
          // cofactor
          vars[ciNum] = toLitCond(xOnI, 0);
          vars[ciNum + 1] = toLitCond(xOffI, 1);
        }
      }

      // test postive unate
      // f
      int outOnI = pCnfOn->pVarNums[outId];
      int outOffI = pCnfOff->pVarNums[outId];
      vars[ciNum + 2] = toLitCond(outOnI, 1);
      vars[ciNum + 3] = toLitCond(outOffI, 0);
      int statusPos = sat_solver_solve(pSat, vars, vars + (ciNum + 4), 0, 0, 0, 0);
      Aig_Obj_t *aigObj = Aig_ManCi(pMan, j);
      if (statusPos == -1)
      {
        idToIsPosUnate[aigObj->Id] = (statusPos == -1);
      }

      // test negative unate
      // f
      outOnI = pCnfOn->pVarNums[outId];
      outOffI = pCnfOff->pVarNums[outId];
      vars[ciNum + 2] = toLitCond(outOnI, 0);
      vars[ciNum + 3] = toLitCond(outOffI, 1);
      int statusNeg = sat_solver_solve(pSat, vars, vars + (ciNum + 4), 0, 0, 0, 0);
      aigObj = Aig_ManCi(pMan, j);
      if (statusNeg == -1)
      {
        idToIsNegUnate[aigObj->Id] = (statusNeg == -1);
      }
    }
    // 3. Print res
    // record posunate, negunate, binate
    set<size_t> posUnateSet;
    set<size_t> negUnateSet;
    set<size_t> binateSet;
    size_t sumBinate = 0;
    size_t sumPosUnate = 0;
    size_t sumNegUnate = 0;
    for (std::map<size_t, string>::iterator it = globalIdToName.begin(); it != globalIdToName.end(); ++it)
    {
      string curName = it->second;
      // If in support
      if (localNameToId.find(curName) != localNameToId.end())
      {
        size_t curId = localNameToId[curName];
        if (idToIsPosUnate.find(curId) != idToIsPosUnate.end())
        {
          posUnateSet.insert(it->first);
          sumPosUnate++;
        }
        if (idToIsNegUnate.find(curId) != idToIsNegUnate.end())
        {
          negUnateSet.insert(it->first);
          sumNegUnate++;
        }
        if ((idToIsPosUnate.find(curId) == idToIsPosUnate.end()) && (idToIsNegUnate.find(curId) == idToIsNegUnate.end()))
        {
          binateSet.insert(it->first);
          sumBinate++;
        }
      }
      // Not in support
      else
      {
        posUnateSet.insert(it->first);
        negUnateSet.insert(it->first);
        sumPosUnate++;
        sumNegUnate++;
      }
    }
    // Print positive unate
    size_t cntPosUnate = 0;
    for (std::set<size_t>::iterator it = posUnateSet.begin(); it != posUnateSet.end(); ++it)
    {
      if (cntPosUnate == 0)
      {
        cout << "+unate inputs: ";
      }

      if (cntPosUnate == sumPosUnate - 1)
      {
        cout << globalIdToName[*it] << endl;
      }
      else
      {
        cout << globalIdToName[*it] << ",";
      }
      cntPosUnate++;
    }
    // Print negative unate
    size_t cntNegUnate = 0;
    for (std::set<size_t>::iterator it = negUnateSet.begin(); it != negUnateSet.end(); ++it)
    {
      if (cntNegUnate == 0)
      {
        cout << "-unate inputs: ";
      }

      if (cntNegUnate == sumNegUnate - 1)
      {
        cout << globalIdToName[*it] << endl;
      }
      else
      {
        cout << globalIdToName[*it] << ",";
      }
      cntNegUnate++;
    }
    // Print binate
    size_t cntBinate = 0;
    for (std::set<size_t>::iterator it = binateSet.begin(); it != binateSet.end(); ++it)
    {
      if (cntBinate == 0)
      {
        cout << "binate inputs: ";
      }

      if (cntBinate == sumBinate - 1)
      {
        cout << globalIdToName[*it] << endl;
      }
      else
      {
        cout << globalIdToName[*it] << ",";
      }
      cntBinate++;
    }
  }
  // cout << "Avg var: " << cntVar*1.0/Abc_NtkPoNum(pNtk) << endl;
  // std::cout << "avg time diff: " << float( clock () - begin_time ) /  CLOCKS_PER_SEC*1.0/Abc_NtkPoNum(pNtk) << endl;
  // std::cout << "total time diff: " << float( clock () - begin_time ) /  CLOCKS_PER_SEC << endl;
}
// lsv_print_pounate

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
  Lsv_NtkPrintNodes(pNtk, argc, argv);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}