#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <iostream>
#include <algorithm>
#include <map>
#include "base/abc/abc.h"
#include "aig/aig/aig.h"
#include "sat/cnf/cnf.h"


using namespace std;

static int Lsv_CommandPrintPOunate(Abc_Frame_t* pAbc, int argc, char** argv);

extern "C" {
  extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t *, int , int );
  extern Cnf_Dat_t *     Cnf_DataDup( Cnf_Dat_t * p );
}
map<string, int> mp;  // <name, type> type&2 == 2 : +unate, type&1 == 1 : -unate
bool comp(Abc_Obj_t* a, Abc_Obj_t* b) {return Abc_ObjId(a) < Abc_ObjId(b);};
vector<Abc_Obj_t*> original_pi;

int n;
sat_solver * Lsv_GetSolver(Aig_Man_t *pMan, Cnf_Dat_t *pCnf) {
  sat_solver * pSat = sat_solver_new();
  sat_solver_setnvars(pSat, 2 * n + Aig_ManCiNum(pMan));
  // add first copy of CNF to pSat
  for (int i = 0; i < pCnf->nClauses; i++) {
    sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] );
  }
  // add second copy of CNF to pSat
  Cnf_DataLift(pCnf, n); 
  for (int i = 0; i < pCnf->nClauses; i++) {
    sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] );
  }
  Cnf_DataLift(pCnf, -n);
  // add PI equality clauses
  int i, Var;
  Aig_Obj_t * pObj;
  Aig_ManForEachCi(pMan, pObj, i) {
    Var = pCnf->pVarNums[pObj->Id];
    //sat_solver_addvar(pSat);
    sat_solver_add_buffer_enable(pSat, Var, n + Var, 2 * n + i, 0); //buffer enable variable = 2 * n + 1
  }
  return pSat;
}
void Lsv_NtkPrintPOunateOneOut(Abc_Ntk_t * pNtk, unsigned inv) {
  int i = 0, Var, i_po;
  Aig_Obj_t * pObj;
  Abc_Obj_t *pObj2;
  Aig_Man_t *pMan = Abc_NtkToDar(pNtk, 0, 0);
  Cnf_Dat_t *pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
  n = pCnf->nVars;
  string po;
  Abc_NtkForEachPo(pNtk, pObj2, i_po) { 
    po = Abc_ObjName(pObj2); //get the po name
  }
  vector<int> pi, alpha; //pi_var, buffer_enable_var
  Aig_ManForEachCi(pMan, pObj, i) {
    Var = pCnf->pVarNums[pObj->Id];
    alpha.push_back(2 * n + i); //store the buffer enable variable array
    pi.push_back(Var);  //store the pi variable array
  }
  ABC_INT64_T a = 0, b = 0, c = 0, d = 0;
  lit Lits[alpha.size() + 4];
  Aig_ManForEachCo(pMan, pObj, i_po) {
    Var = pCnf->pVarNums[pObj->Id];
    cout << "node " << po << ":\n";  
    vector<Abc_Obj_t *> pos, neg, bi;
    if (pi.size() > 20) {  //add po constrains to solver befor simplify
      //         +unate solver                        -unate solver           
      sat_solver *pSat_p = Lsv_GetSolver(pMan, pCnf), *pSat_n = Lsv_GetSolver(pMan, pCnf);
      Lits[0] = toLitCond(Var, 1); //pos output = 0
      sat_solver_addclause(pSat_p, Lits, Lits + 1); 
      Lits[0] = toLitCond(Var + n, 0); //neg output = 1
      sat_solver_addclause(pSat_p, Lits, Lits + 1); 
      //sat_solver_simplify(pSat_p);  
      Lits[0] = toLitCond(Var, 0); //pos output = 1
      sat_solver_addclause(pSat_n, Lits, Lits + 1); 
      Lits[0] = toLitCond(Var + n, 1); //neg output = 0
      sat_solver_addclause(pSat_n, Lits, Lits + 1); 
      //sat_solver_simplify(pSat_n);  
      for (int i0 = 0; i0 < alpha.size(); i0++) {
        Lits[i0] = toLitCond(alpha[i0] ,0);
      }
      Abc_NtkForEachPi(pNtk, pObj2, i) { 
        Lits[i] = toLitCond(alpha[i] ,1);
        Lits[alpha.size()] = toLitCond(pi[i], 0);
        Lits[alpha.size() + 1] = toLitCond(pi[i] + n, 1);
        //pos unate 
        int result_p = sat_solver_solve(pSat_p, Lits, Lits + alpha.size() + 2, a, b, c, d);
        if (result_p != -1) { 
          mp[Abc_ObjName(pObj2)] &= 1;
        }
        //neg unate 
        int result_n = sat_solver_solve(pSat_n, Lits, Lits + alpha.size() + 2, a, b, c, d);
        if (result_n != -1) { 
          mp[Abc_ObjName(pObj2)] &= 2;
        }
        Lits[i] = toLitCond(alpha[i] ,0);
      }
      sat_solver_delete(pSat_n); sat_solver_delete(pSat_p);
    } else {  // solve with base line method
      sat_solver *pSat = Lsv_GetSolver(pMan, pCnf);
      //sat_solver_simplify(pSat);  
      for (int i0 = 0; i0 < alpha.size(); i0++) {
        Lits[i0] = toLitCond(alpha[i0] ,0);
      }
      Abc_NtkForEachPi(pNtk, pObj2, i) { 
        Lits[i] = toLitCond(alpha[i] ,1);
        Lits[alpha.size()] = toLitCond(pi[i], 0);
        Lits[alpha.size() + 1] = toLitCond(pi[i] + n, 1);
        //pos unate 
        Lits[alpha.size() + 2] = toLitCond(Var, 1); //pos output = 0
        Lits[alpha.size() + 3] = toLitCond(Var + n, 0); //neg output = 1
        int result_p = sat_solver_solve(pSat, Lits, Lits + alpha.size() + 4, a, b, c, d);
        if (result_p != -1) { 
          mp[Abc_ObjName(pObj2)] &= 1;
        }
        //neg unate 
        Lits[alpha.size() + 2] = toLitCond(Var, 0); //pos output = 1
        Lits[alpha.size() + 3] = toLitCond(Var + n, 1); //neg output = 0
        int result_n = sat_solver_solve(pSat, Lits, Lits + alpha.size() + 4, a, b, c, d);
        if (result_n != -1) { 
          mp[Abc_ObjName(pObj2)] &= 2;
        }
        Lits[i] = toLitCond(alpha[i] ,0);
      }
      sat_solver_delete(pSat);
    }
    for(int i = 0; i < original_pi.size(); i++) {
      int temp =  mp[Abc_ObjName(original_pi[i])];
      if (temp == 0) bi.push_back(original_pi[i]);
      if (temp & 2) pos.push_back(original_pi[i]);
      if (temp & 1) neg.push_back(original_pi[i]);
    }

    if (inv == 1) swap(pos, neg);
    if (!pos.empty()) {
      cout << "+unate inputs: ";
      for (int i = 0; i < pos.size(); i++) cout << Abc_ObjName(pos[i]) << (i == pos.size() - 1 ? '\n': ',');
    }
    if (!neg.empty()) {
      cout << "-unate inputs: ";
      for (int i = 0; i < neg.size(); i++) cout << Abc_ObjName(neg[i]) << (i == neg.size() - 1 ? '\n': ',');
    }
    if (!bi.empty()) {
      cout << "binate inputs: ";
      for (int i = 0; i < bi.size(); i++) cout << Abc_ObjName(bi[i]) << (i == bi.size() - 1 ? '\n': ',');
    }
  }
  Cnf_DataFree(pCnf);
  Aig_ManStop(pMan);
  Abc_NtkDelete(pNtk);
}

void Lsv_NtkPrintPOunate(Abc_Ntk_t * pNtk) {
  Abc_Obj_t *pObj;
  int i_po, i;
  mp.clear();
  Abc_NtkForEachPi(pNtk, pObj, i) {
    original_pi.push_back(pObj);  //store pi node into original_pi
    mp[Abc_ObjName(pObj)] = 0;  //stroe pi name to mp
  }
  sort(original_pi.begin(), original_pi.end(), comp); //sort the pi
  Abc_NtkForEachCo(pNtk, pObj, i_po) { //Solve each PO
    for (map<string, int>::iterator it = mp.begin(); it != mp.end(); ++it) it->second = 3;
    Lsv_NtkPrintPOunateOneOut(Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pObj), Abc_ObjName(pObj),0), pObj->fCompl0);
  }
}

int Lsv_CommandPrintPOunate(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintPOunate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
  Abc_Print(-2, "\t        prints the unate of output nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
