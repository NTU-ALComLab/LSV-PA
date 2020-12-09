#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <string>
#include <iostream>
#include <set>
#include <algorithm>
#include <unordered_map>
#include "proof/fra/fra.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
extern "C"
{
  //告訴編譯器，這部分程式碼按C語言的格式進行編譯，而不是C++的

  Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
  void Cnf_DataLift(Cnf_Dat_t *p, int nVarsPlus);
  //Abc_Ntk_t *        Abc_NtkCreateCone( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, char * pNodeName, int fUseAllCis );
}

using namespace std;

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

int Lsv_CommandPrintNodes(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk_origin = Abc_FrameReadNtk(pAbc);
  if (!pNtk_origin)
  {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  Abc_Obj_t *pCo_origin;
  int o;

  Abc_NtkForEachCo(pNtk_origin, pCo_origin, o)
  {
    //take the fanin of PO, because po is special node cannot be used
    Abc_Obj_t *pCo;
    pCo = Abc_ObjFanin0(pCo_origin);
    cout << "node " << Abc_ObjName(pCo_origin) << ":" << endl;

    //if return 1 means complement for PO
    int complement = Abc_ObjFaninC0(pCo_origin);

    Abc_Ntk_t *pNtk = Abc_NtkCreateCone(pNtk_origin, pCo, Abc_ObjName(pCo_origin), 0);
    //mapping problem, mapping the ci seqence from cone to network
    //Abc_NtkPi( Abc_Ntk_t * pNtk, int i ) get PI info
    unordered_map<int, int> umap;
    Abc_Obj_t *pCi_origin, *pCi_cone;
    int cone, cone_i, matched;
    vector<int> pos_unate;
    vector<int> neg_unate;
    vector<int> binate;
    pos_unate.clear();
    neg_unate.clear();
    binate.clear();
    umap.clear();
    Abc_NtkForEachCi(pNtk_origin, pCi_origin, cone)
    {
      matched = 0;
      Abc_NtkForEachCi(pNtk, pCi_cone, cone_i)
      {
        matched = 0;
        if (strcmp((Abc_ObjName(pCi_origin)), (Abc_ObjName(pCi_cone))) == 0)
        {
          matched = 1;
          umap[cone_i] = cone;
          break;
        }
      }

      if (matched == 0)
      {
        // cout << Abc_ObjName(pCi_origin) << " " << matched << " ";
        pos_unate.push_back(cone);
        neg_unate.push_back(cone);
      }
    }

    //pNtk to aig_man network
    Aig_Man_t *pMan;
    pMan = Abc_NtkToDar(pNtk, 0, 0);
    //cout << " read aig file success !!!" << endl;

    //create two identical cnf network
    Cnf_Dat_t *pCnf_pos;
    Cnf_Dat_t *pCnf_neg;
    pCnf_pos = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    //cout << " create two identical cnf network success !!!" << endl;

    //negitive network change id (use extern void Cnf_DataLift( Cnf_Dat_t * p, int nVarsPlus );)
    pCnf_neg = Cnf_DataDup(pCnf_pos);
    Cnf_DataLift(pCnf_neg, pCnf_neg->nVars); //why is aig var num???
    //cout << " Cnf_DataLift success !!!" << endl;

    //sat solver
    sat_solver *pSat;

    //cnf write into solver
    pSat = sat_solver_new();
    sat_solver_setnvars(pSat, (pCnf_pos->nVars) * 2);
    //cout << " cnf write into solver success !!!" << endl;

    //add each clause in cnf_pos and cnf_neg ( sat_solver_addclause(sat_solver* s, lit* begin, lit* end)  )
    for (int i = 0; i < (pCnf_pos->nClauses); i++)
    {
      sat_solver_addclause(pSat, pCnf_pos->pClauses[i], pCnf_pos->pClauses[i + 1]);
      sat_solver_addclause(pSat, pCnf_neg->pClauses[i], pCnf_neg->pClauses[i + 1]);
    }

    // create enable variable
    int i;
    int *alpha = new int[Abc_NtkCiNum(pNtk)];
    //cout << "create enable variable success !!!" << endl;

    //enable all nodes by alpha
    Aig_Obj_t *pCi;
    // cout<<"aig ci => ";
    Aig_ManForEachCi(pMan, pCi, i)
    {
      alpha[i] = sat_solver_addvar(pSat);
      sat_solver_add_buffer_enable(pSat, pCnf_pos->pVarNums[Aig_ObjId(pCi)], pCnf_neg->pVarNums[Aig_ObjId(pCi)], alpha[i], 0);
    }

    //incremental sat solver
    Aig_ManForEachCi(pMan, pCi, i)
    {
      //assumptions
      int *assumption = new int[Abc_NtkCiNum(pNtk) + 4];
      for (int j = 0; j < Abc_NtkCiNum(pNtk); j++)
      {
        if (j == i)
        {
          assumption[j] = Abc_Var2Lit(alpha[j], 1);
        }
        else
        {
          assumption[j] = Abc_Var2Lit(alpha[j], 0);
        }
      }
      //check positive unate
      assumption[Abc_NtkCiNum(pNtk) + 0] = Abc_Var2Lit(pCnf_pos->pVarNums[Aig_ObjId(pCi)], 1);
      assumption[Abc_NtkCiNum(pNtk) + 1] = Abc_Var2Lit(pCnf_neg->pVarNums[Aig_ObjId(pCi)], 0);
      assumption[Abc_NtkCiNum(pNtk) + 2] = Abc_Var2Lit(pCnf_pos->pVarNums[Aig_ObjId(Aig_ManCo(pMan, 0))], 0);
      assumption[Abc_NtkCiNum(pNtk) + 3] = Abc_Var2Lit(pCnf_neg->pVarNums[Aig_ObjId(Aig_ManCo(pMan, 0))], 1);

      int posunate = sat_solver_solve(pSat, assumption, assumption + Abc_NtkCiNum(pNtk) + 4, 0, 0, 0, 0);
      if (posunate == -1) //UNSAT
      {
        pos_unate.push_back(umap[i]);
      }

      //check negitive unate
      assumption[Abc_NtkCiNum(pNtk) + 0] = Abc_Var2Lit(pCnf_pos->pVarNums[Aig_ObjId(pCi)], 0);
      assumption[Abc_NtkCiNum(pNtk) + 1] = Abc_Var2Lit(pCnf_neg->pVarNums[Aig_ObjId(pCi)], 1);
      assumption[Abc_NtkCiNum(pNtk) + 2] = Abc_Var2Lit(pCnf_pos->pVarNums[Aig_ObjId(Aig_ManCo(pMan, 0))], 0);
      assumption[Abc_NtkCiNum(pNtk) + 3] = Abc_Var2Lit(pCnf_neg->pVarNums[Aig_ObjId(Aig_ManCo(pMan, 0))], 1);

      int negunate = sat_solver_solve(pSat, assumption, assumption + Abc_NtkCiNum(pNtk) + 4, 0, 0, 0, 0);
      if (negunate == -1) //UNSAT
      {
        neg_unate.push_back(umap[i]);
      }

      if (posunate == 1 && negunate == 1)
      {
        binate.push_back(umap[i]);
      }
      //cout << " node = " << Abc_ObjName(Abc_NtkPi(pNtk_origin, umap[i]));
    }

    //outpout format
    std::sort(pos_unate.begin(), pos_unate.end());
    std::sort(neg_unate.begin(), neg_unate.end());
    std::sort(binate.begin(), binate.end());
    if (complement == 0)
    {
      if (pos_unate.size() > 0)
      {
        cout << "+unate inputs: ";
        int pos_unate_size = pos_unate.size();
        for (size_t i = 0; i < pos_unate_size; ++i)
        {
          cout << Abc_ObjName(Abc_NtkPi(pNtk_origin, pos_unate.at(i)));
          if (i != pos_unate_size - 1)
          {
            cout << ",";
          }
          else
          {
            cout << endl;
          }
        }
      }
      if (neg_unate.size() > 0)
      {
        cout << "-unate inputs: ";
        int neg_unate_size = neg_unate.size();
        for (size_t i = 0; i < neg_unate_size; ++i)
        {
          cout << Abc_ObjName(Abc_NtkPi(pNtk_origin, neg_unate.at(i)));
          if (i != neg_unate_size - 1)
          {
            cout << ",";
          }
          else
          {
            cout << endl;
          }
        }
      }
      if (binate.size() > 0)
      {
        cout << "binate inputs: ";
        int binate_size = binate.size();
        for (size_t i = 0; i < binate_size; ++i)
        {
          cout << Abc_ObjName(Abc_NtkPi(pNtk_origin, binate.at(i)));
          if (i != binate_size - 1)
          {
            cout << ",";
          }
          else
          {
            cout << endl;
          }
        }
      }
    }
    else
    {
      if (neg_unate.size() > 0)
      {
        cout << "+unate inputs: ";
        int neg_unate_size = neg_unate.size();
        for (size_t i = 0; i < neg_unate_size; ++i)
        {
          cout << Abc_ObjName(Abc_NtkPi(pNtk_origin, neg_unate.at(i)));
          if (i != neg_unate_size - 1)
          {
            cout << ",";
          }
          else
          {
            cout << endl;
          }
        }
      }
      if (pos_unate.size() > 0)
      {
        cout << "-unate inputs: ";
        int pos_unate_size = pos_unate.size();
        for (size_t i = 0; i < pos_unate_size; ++i)
        {
          cout << Abc_ObjName(Abc_NtkPi(pNtk_origin, pos_unate.at(i)));
          if (i != pos_unate_size - 1)
          {
            cout << ",";
          }
          else
          {
            cout << endl;
          }
        }
      }
      if (binate.size() > 0)
      {
        cout << "binate inputs: ";
        int binate_size = binate.size();
        for (size_t i = 0; i < binate_size; ++i)
        {
          cout << Abc_ObjName(Abc_NtkPi(pNtk_origin, binate.at(i)));
          if (i != binate_size - 1)
          {
            cout << ",";
          }
          else
          {
            cout << endl;
          }
        }
      }
    }
  }
  return 0;
}