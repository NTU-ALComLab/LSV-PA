#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "proof/fraig/fraig.h"
#include "opt/fxu/fxu.h"
#include "opt/fxch/Fxch.h"
#include "opt/cut/cut.h"
#include "map/fpga/fpga.h"
#include "map/if/if.h"
#include "opt/sim/sim.h"
#include "opt/res/res.h"
#include "opt/lpk/lpk.h"
#include "aig/gia/giaAig.h"
#include "opt/dar/dar.h"
#include "opt/mfs/mfs.h"
#include "proof/fra/fra.h"
#include "aig/saig/saig.h"
#include "proof/int/int.h"
#include "proof/dch/dch.h"
#include "proof/ssw/ssw.h"
#include "opt/cgt/cgt.h"
#include "bool/kit/kit.h"
#include "map/amap/amap.h"
#include "opt/ret/retInt.h"
#include "sat/xsat/xsat.h"
#include "sat/satoko/satoko.h"
#include "sat/cnf/cnf.h"
#include "proof/cec/cec.h"
#include "proof/acec/acec.h"
#include "proof/pdr/pdr.h"
#include "misc/tim/tim.h"
#include "bdd/llb/llb.h"
#include "bdd/bbr/bbr.h"
#include "map/cov/cov.h"
#include "base/cmd/cmd.h"
#include "proof/abs/abs.h"
#include "sat/bmc/bmc.h"
#include "proof/ssc/ssc.h"
#include "opt/sfm/sfm.h"
#include "opt/sbd/sbd.h"
#include "bool/rpo/rpo.h"
#include "map/mpm/mpm.h"
#include "opt/fret/fretime.h"
#include "opt/nwk/nwkMerge.h"
#include "base/acb/acbPar.h"
#include <vector>
#include <iostream>
#include <sstream> 
#include <string>
#include <regex>
#include <assert.h>
#include <algorithm>
#include <unordered_map>


using namespace std;
extern "C"
{
    Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
}
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv);
static Cnf_Man_t * s_pManCnf = NULL;
static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPounate, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPo(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
  Abc_NtkForEachPi(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}
bool compare(pair< Abc_Obj_t*, short> a, pair< Abc_Obj_t*, short> b) {
  return Abc_ObjId(a.first) < Abc_ObjId(b.first);
}

//TODO
void Lsv_NtkPrintPounate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* poObj;// Po iteration
  int poIter;
  Abc_NtkForEachPo(pNtk, poObj, poIter){
    unordered_map<string, int> Pi_unateness_mapping;
    printf("node %s:\n", Abc_ObjName(poObj));
    
    auto cone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(poObj), Abc_ObjName(poObj), 0);;
    auto pMan = Abc_NtkToDar( cone, 0, 0 );
    auto pCnf_p = Cnf_Derive(pMan, Aig_ManCoNum(pMan)); //positive cofactor
    auto pCnf_n = Cnf_DataDup(pCnf_p);                  //negative cofactor
    Cnf_DataLift(pCnf_n, pCnf_p-> nVars);

    sat_solver *pSat = (sat_solver *)Cnf_DataWriteIntoSolver(pCnf_p, 1, 0);                     //solver
    sat_solver_setnvars(pSat, pCnf_n->nVars);
    for(int iter = 0; iter < pCnf_n->nClauses; ++iter){
      sat_solver_addclause(pSat, pCnf_n->pClauses[iter], pCnf_n->pClauses[iter + 1]);
    }

    Aig_Obj_t* aig_piObj;// Pi iteration
    int piIter;
    vector<int> enablingVar(Aig_ManCiNum(pMan)); // store enabling var in sat solver
    Aig_ManForEachCi(pMan, aig_piObj, piIter){
      auto piObjId = Aig_ObjId(aig_piObj);
      enablingVar[piIter] = sat_solver_addvar(pSat);
      sat_solver_add_buffer_enable(pSat, pCnf_p-> pVarNums[piObjId], pCnf_n-> pVarNums[piObjId], enablingVar[piIter], 0);
    }

    vector<int> assummption(Aig_ManCiNum(pMan) + 4);
    Aig_ManForEachCi(pMan, aig_piObj, piIter){
      assummption[piIter] = toLitCond(enablingVar[piIter], 0);
    }

    Abc_Obj_t * piObj;
    auto PoAigObj = Aig_ManCo(pMan, 0);
    Abc_NtkForEachPi(cone, piObj, piIter){// sat_solver solver for each pi
      assummption[piIter] = toLitCond(enablingVar[piIter], 1);
      assummption[Aig_ManCiNum(pMan)] = toLitCond(pCnf_p-> pVarNums[Abc_ObjId(piObj)], 0);
      assummption[Aig_ManCiNum(pMan) + 1] = toLitCond(pCnf_n-> pVarNums[Abc_ObjId(piObj)], 1);
      // solve for positive unate
      assummption[Aig_ManCiNum(pMan) + 2] = toLitCond(pCnf_p-> pVarNums[Aig_ObjId(PoAigObj)], 1);
      assummption[Aig_ManCiNum(pMan) + 3] = toLitCond(pCnf_n-> pVarNums[Aig_ObjId(PoAigObj)], 0);
      auto positive_unate = sat_solver_solve(pSat, &*assummption.begin(), &*assummption.end(), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

      // solve for negative unate
      assummption[Aig_ManCiNum(pMan) + 2] = toLitCond(pCnf_p-> pVarNums[Aig_ObjId(PoAigObj)], 0);
      assummption[Aig_ManCiNum(pMan) + 3] = toLitCond(pCnf_n-> pVarNums[Aig_ObjId(PoAigObj)], 1);
      auto negative_unate = sat_solver_solve(pSat, &*assummption.begin(), &*assummption.end(), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
      
      if (poObj ->fCompl0) swap(positive_unate, negative_unate);
      if (positive_unate == l_False && negative_unate == l_False)
        Pi_unateness_mapping[Abc_ObjName(piObj)] = 3;
      else if(positive_unate == l_False)
        Pi_unateness_mapping[Abc_ObjName(piObj)] = 0;
      else if(negative_unate == l_False)
        Pi_unateness_mapping[Abc_ObjName(piObj)] = 1;
      else
        Pi_unateness_mapping[Abc_ObjName(piObj)] = 2;
      assummption[piIter] = toLitCond(enablingVar[piIter], 0); // re_assign to 1
    }
    vector<string> binate;
    vector<string> positiveUnate;
    vector<string> negativeUnate;
    piObj = NULL;// Po iteration
    Abc_NtkForEachPi(pNtk, piObj, piIter){
      auto got = Pi_unateness_mapping.find(Abc_ObjName(piObj));
      if( got == Pi_unateness_mapping.end() ){
        // cout << Abc_ObjName(piObj) << " not found" << endl;
        positiveUnate.push_back(Abc_ObjName(piObj));
        negativeUnate.push_back(Abc_ObjName(piObj));
      }
      else{
        // cout << Abc_ObjName(piObj) << " got " << got-> second << endl;
        if (got-> second == 0) positiveUnate.push_back(Abc_ObjName(piObj));
        else if (got-> second == 1) negativeUnate.push_back(Abc_ObjName(piObj));
        else if (got-> second == 2) binate.push_back(Abc_ObjName(piObj));
        else if (got-> second == 3){
          positiveUnate.push_back(Abc_ObjName(piObj));
          negativeUnate.push_back(Abc_ObjName(piObj));
        }
      }
    }
    if(binate.size() + positiveUnate.size() + negativeUnate.size() == 0) cout <<"binate inputs:" << endl;
    else{
      if (positiveUnate.size() != 0 ){
        cout << "+unate inputs: ";
        for ( auto x:positiveUnate){
          if( x != positiveUnate[0]) cout << ',';
          cout << x;
        }
        cout << endl;
      }
      if (negativeUnate.size() != 0 ){
        cout << "-unate inputs: ";
        for ( auto x:negativeUnate){
          if( x != negativeUnate[0]) cout << ',';
          cout << x;
        }
        cout << endl;
      }
      if (binate.size() != 0 ){
        cout << "binate inputs: ";
        for ( auto x:binate){
          if( x != binate[0]) cout << ',';
          cout << x;
        }
        cout << endl;
      }
    } 
  }
}
void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_Obj_t* pObj_copy;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    pObj_copy = pObj;
    Abc_Obj_t* pFanin;
    int j;
    vector< pair< Abc_Obj_t*, short>  > allFanin; // int==0 means neg, int==1 means pos, int==2 means bi, int==3 means error
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      Abc_ObjForEachFanin(pObj, pFanin, j) {
        allFanin.push_back(make_pair(pFanin, 3));
      }
      if (Abc_NtkHasSop(pNtk)) {
        string s = (string)(char*)pObj->pData;
        regex newline{R"(\n+)"};
        regex whitespace{R"(\s+)"};
        sregex_token_iterator it{s.begin(), s.end(), newline, -1};
        vector<string> lines{it, {}};
        bool on = 0;
        for ( string const str: lines){
          sregex_token_iterator it{str.begin(), str.end(), whitespace, -1};
          vector<string> toks{it, {}};
          assert( toks.size() == 2);
          stringstream sstr1( toks[1] ); 
          assert( toks[1].length() == 1);
          sstr1 >> on;
          assert( toks[0].length() == allFanin.size() );
          for( int i = 0; i < toks[0].length(); ++i){
            if ( toks[0][i] == '0' ){
              if ( allFanin[i].second == 3) allFanin[i].second = -1;
              else if ( allFanin[i].second == 1) allFanin[i].second = 2;
            }
            else if ( toks[0][i] == '1' ){
              if ( allFanin[i].second == 3) allFanin[i].second = 1;
              else if ( allFanin[i].second == -1) allFanin[i].second = 2;
            }
          }
        }
        if ( !on ){
          for ( auto& it: allFanin){
            if( it.second == 2)continue;
            it.second *= -1;
          }
        }
      }
    }

    if (allFanin.size() == 0) return;
    sort(allFanin.begin(),allFanin.end(), compare);
    printf("node %s:\n", Abc_ObjName(pObj_copy));
    vector<Abc_Obj_t*> Fanin2BPrinted;
    for ( short nateType: {1,-1,2}){
      Fanin2BPrinted.clear();
      for( auto& Fanin: allFanin)
        if ( Fanin.second == nateType) Fanin2BPrinted.push_back( Fanin.first);
      if ( Fanin2BPrinted.size() == 0) continue;
      else{
        if ( nateType == -1 ) cout << "-unate inputs: ";
        else if ( nateType == 1 ) cout << "+unate inputs: ";
        else if ( nateType == 2 ) cout << "binate inputs: ";
        cout << Abc_ObjName(Fanin2BPrinted[0]);
        Fanin2BPrinted.erase(Fanin2BPrinted.begin());
      }
      for( auto& Fanin: Fanin2BPrinted)
        cout << ',' << Abc_ObjName(Fanin);
      cout << '\n';
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  vector< int > vec_int;

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
  Lsv_NtkPrintSopunate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  vector< int > vec_int;

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
  Lsv_NtkPrintPounate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

