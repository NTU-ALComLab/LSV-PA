#ifndef LSV_HPP
#define LSV_HPP

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <iostream>
#include <map>
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver2.h"
#include "proof/fra/fra.h"
#include <unordered_map>

using namespace std;

#define MINISAT
// #define GLUCOSE

class Network;

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv);


void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk);
void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk);
void Lsv_NtkPrintPounate(Abc_Ntk_t* pNtk);
int lsv_solve(void* pSat, int *lits, int nvar);
void lsv_printResult(Network* pNetwork);

class Network{
public:
  Network(Abc_Ntk_t* p): _pNtk(p), _pNtkConeTrue(NULL), _nPi(Abc_NtkPiNum(_pNtk))
  {
    int i;
    vector<bool> val(2,0);
    Abc_Obj_t * pNode;
    Abc_NtkForEachPi(_pNtk, pNode, i){
      _mId2name[Abc_ObjId(pNode)] = Abc_ObjName(pNode);
    }
    Abc_NtkForEachPi(_pNtk, pNode, i){
      _mName2val[Abc_ObjName(pNode)] = val;
    }
  };
  ~Network(){};
  void setpNtkCone(Abc_Obj_t* pFanout);
  void* lsv_writeCnf2Solver();

  Abc_Ntk_t* _pNtk;
  Abc_Ntk_t* _pNtkConeTrue;
  Aig_Man_t * _pManT;
  Cnf_Dat_t * _pCnfT;
  Abc_Obj_t * _pcurPoNode;
  int _nCPi;
  int _nPi;
  int _nVar;
  int _newVar;   // index of first alpha
  int _nVarTPi;  // index of first pi of CNFT
  int _nVarFPi;
  map<int, string> _mId2name;
  map<string, vector<bool> > _mName2val;

};

#endif