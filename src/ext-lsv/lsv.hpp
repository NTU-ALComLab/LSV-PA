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
#include <climits>

using namespace std;

// #define MINISAT
#define GLUCOSE
// #define DEBUG
extern "C" {
    Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    Abc_Ntk_t * Abc_NtkDarFraig( Abc_Ntk_t * pNtk, int nConfLimit, int fDoSparse, int fProve, int fTransfer, int fSpeculate, int fChoicing, int fVerbose );
}

class Network;

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv);


void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk);
void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk);
void Lsv_NtkPrintPounate(Abc_Ntk_t* pNtk);
int lsv_solve(void* pSat, int *lits, int nvar);

class Network{
public:
  Network(Abc_Ntk_t* p): _pNtkConeTrue(NULL), _nPi(Abc_NtkPiNum(_pNtk))
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
    _pNtk = Abc_NtkDarFraig( p, 100, 1, 0, 0, 0, 0, 0 );
    _pAig = Abc_NtkToDar( _pNtk, 0, 0 );
  };
  ~Network(){};
  int setpNtkCone(Abc_Obj_t* pFanout);
  void* lsv_writeCnf2Solver();
  void lsv_printResult();

  Abc_Ntk_t* _pNtk;
  Abc_Ntk_t* _pNtkConeTrue;
  Aig_Man_t * _pAig;
  Aig_Man_t * _pManT;
  Cnf_Dat_t * _pCnfT;
  Abc_Obj_t * _pcurPoNode;
  Abc_Obj_t * _pCurNode;
  int _nCPi;
  int _nPi;
  int _nVar;
  int _newVar;   // index of first alpha
  int _nVarTPi;  // index of first pi of CNFT
  int _nVarFPi;
  int _coId;
  map<int, string> _mId2name;
  map<string, vector<bool> > _mName2val;

};

#endif