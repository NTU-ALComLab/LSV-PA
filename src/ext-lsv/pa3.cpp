#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "aig/aig/aig.h"
#include "proof/dch/dch.h"


#include <iostream>
#include <list>
#include <vector>
#include <cstring>
using namespace std;

extern "C" {Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );}
static int Lsv_CommandPrintUnates(Abc_Frame_t* pAbc, int argc, char** argv);

void Lsv_NtkPrintUnates(Abc_Ntk_t* pNtk) {
  int i=0,j=0,k=0,m=0,n=0,u=0,v=0,w=0;
  int flag=0;
  Abc_Obj_t * pCo, *pCi2;
  Aig_Obj_t * pCi, *pCo2;
  Abc_Ntk_t * pNtkRes;
  Aig_Man_t * pAig;
  Cnf_Dat_t * pCnf, *pCnf2;
  int status, status2;
  vector <int> allid;
  vector <char*> alllist;
  vector <char*> conelist;
  Abc_NtkForEachCo(pNtk, pCo, i) {
    Abc_NtkForEachCi( pNtk, pCi2, v){
      alllist.push_back(Abc_ObjName(pCi2));
      allid.push_back(Abc_ObjId(pCi2));
    }
    int key, sortind;
    char* charkey;
    for(int w=1;w<allid.size();w++){
      key = allid.at(w);
      charkey = alllist.at(w);
      sortind = w-1;
      while(sortind>=0&&allid.at(sortind)>key){
        allid.at(sortind+1) = allid.at(sortind);
        alllist.at(sortind+1) = alllist.at(sortind);
        sortind--;
      }
      allid.at(sortind+1) = key;
      alllist.at(sortind+1) = charkey;
    }
    pNtkRes = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(pCo), Abc_ObjName(pCo), 0 );
    if(!Abc_ObjFaninC0(pCo)){
      Abc_ObjSetFaninC(Abc_NtkPo(pNtkRes,0),0);
    }
    Abc_NtkForEachCi( pNtkRes, pCi2, v)
      conelist.push_back(Abc_ObjName(pCi2));
    pAig = Abc_NtkToDar( pNtkRes, 0, 0 );
    pCnf = Cnf_Derive( pAig, 1 );
    pCnf2 = Cnf_DataDup( pCnf );
    Cnf_DataLift( pCnf2, pCnf->nVars );
    int nProblem = (Aig_ManCiNum(pAig));
    int assump[nProblem];
    lit* Lits = ABC_ALLOC( lit , nProblem + 5);
    lit* Lits2 = ABC_ALLOC( lit , nProblem + 5);
    sat_solver *pSat;
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, 2*pCnf->nVars );
    for ( k = 0; k < pCnf->nClauses; k++ ){
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[k], pCnf->pClauses[k+1] ) )
        {
            sat_solver_delete( pSat );
        }
        if ( !sat_solver_addclause( pSat, pCnf2->pClauses[k], pCnf2->pClauses[k+1] ) )
        {
            sat_solver_delete( pSat );
        }
    }
    Aig_ManForEachCi( pAig, pCi, j){
      assump[j] = sat_solver_addvar(pSat);
      sat_solver_add_buffer_enable( pSat, pCnf->pVarNums[Aig_ObjId(pCi)], pCnf2->pVarNums[Aig_ObjId(pCi)], assump[j], 0 );
    }
    cout<<"node "<<Abc_ObjName(pCo)<<":"<<endl;
    vector <char*> poslist;
    vector <char*> neglist;
    vector <char*> bilist;
    vector <char*> poslistnew;
    vector <char*> neglistnew;
    vector <char*> bilistnew;
    Aig_ManForEachCi( pAig, pCi, n){
      for(m=0;m<nProblem;m++){
        if(m==n) Lits[m] = toLitCond( assump[m], 1 );
        else Lits[m] = toLitCond( assump[m], 0 );
        Lits2[m] = Lits[m];
      }
      Lits[nProblem] = toLitCond( pCnf->pVarNums[Aig_ObjId(pCi)], 1 );
      Lits[nProblem+1] = toLitCond( pCnf2->pVarNums[Aig_ObjId(pCi)], 0 );
      Lits2[nProblem] = toLitCond( pCnf->pVarNums[Aig_ObjId(pCi)], 0 );
      Lits2[nProblem+1] = toLitCond( pCnf2->pVarNums[Aig_ObjId(pCi)], 1 );
      Aig_ManForEachCo( pAig, pCo2, u){
        Lits[nProblem+2] = toLitCond( pCnf->pVarNums[Aig_ObjId(pCo2)], 1 );
        Lits[nProblem+3] = toLitCond( pCnf2->pVarNums[Aig_ObjId(pCo2)], 0 );
      }
      Lits2[nProblem+2] = Lits[nProblem+2];
      Lits2[nProblem+3] = Lits[nProblem+3];
      status = sat_solver_solve(pSat, &Lits[0], &Lits[nProblem+4], 50000000, 50000000, 0, 0);
      status2 = sat_solver_solve(pSat, &Lits2[0], &Lits2[nProblem+4], 50000000, 50000000, 0, 0);
      if(status==-1) poslist.push_back(conelist.at(n)); 
      if(status2==-1) neglist.push_back(conelist.at(n)); 
      if(status==1 && status2==1) bilist.push_back(conelist.at(n)); 
    }

    for(u=0;u<alllist.size();u++){
      flag=0;
      for(w=0;w<poslist.size();w++)
        if(strcmp(alllist.at(u), poslist.at(w)) == 0) { 
          poslistnew.push_back(alllist.at(u));
          flag=1;
          break;
        }
      for(w=0;w<neglist.size();w++)
        if(strcmp(alllist.at(u), neglist.at(w)) == 0) {
          neglistnew.push_back(alllist.at(u));
          flag=1;
          break;
        }  
      for(w=0;w<bilist.size();w++)
        if(strcmp(alllist.at(u), bilist.at(w)) == 0) {
          bilistnew.push_back(alllist.at(u));
          flag=1;
          break;
        }
      if(flag==0){
        poslistnew.push_back(alllist.at(u));
        neglistnew.push_back(alllist.at(u));
      }
    }
    if(!poslistnew.empty()) cout<<"+unate inputs: "<<poslistnew.at(0);
    for (w=1; w<poslistnew.size(); w++)
      cout << "," << poslistnew.at(w);
    if(!poslistnew.empty()) cout<<endl;
    if(!neglistnew.empty()) cout<<"-unate inputs: "<<neglistnew.at(0);
    for (w=1; w<neglistnew.size(); w++)
      cout << "," << neglistnew.at(w);
    if(!neglistnew.empty()) cout<<endl;
    if(!bilistnew.empty()) cout<<"binate inputs: "<<bilistnew.at(0);
    for (int w=1; w<bilistnew.size(); w++)
      cout << "," << bilistnew.at(w);
    if(!bilistnew.empty()) cout<<endl;
    Cnf_DataFree( pCnf );
    Cnf_DataFree( pCnf2 );
    allid.clear();
    alllist.clear();
    poslist.clear();
    neglist.clear();
    bilist.clear();
    poslistnew.clear();
    neglistnew.clear();
    bilistnew.clear();
    conelist.clear();
    sat_solver_delete( pSat );
  }
}

int Lsv_CommandPrintUnates(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintUnates(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

// Very simple ABC command: prints a greeting and its command line argumentss
/*int Hello_Command( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    std::cout << "Hello world!" << std::endl;

    for(int i=0; i<argc; i++)
    {
        std::cout << "  argv[" << i << "]: " << argv[i] << std::endl;
    }

    return 0;
}*/

// called during ABC startup
void init(Abc_Frame_t* pAbc)
{
    Cmd_CommandAdd( pAbc, "Unate", "lsv_print_pounate", Lsv_CommandPrintUnates, 0);
}

// called during ABC termination
void destroy(Abc_Frame_t* pAbc)
{
}

// this object should not be modified after the call to Abc_FrameAddInitializer
Abc_FrameInitializer_t frame_initializer = { init, destroy };

// register the initializer a constructor of a global object
// called before main (and ABC startup)
struct registrar
{
    registrar() 
    {
        Abc_FrameAddInitializer(&frame_initializer);
    }
} hello_registrar;



