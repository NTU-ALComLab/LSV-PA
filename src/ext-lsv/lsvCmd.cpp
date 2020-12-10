#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "aig/aig/aig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include <vector>

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbci, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintNodes, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};


struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;
/*
void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
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
}*/


extern "C"
{
  Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}



int Lsv_CommandPrintNodes(Abc_Frame_t* pAbci, int argc, char** argv) {
  Abc_Ntk_t * pAbc = Abc_FrameReadNtk(pAbci);
  int j;
  Abc_Obj_t* pObjCo;

  Abc_NtkForEachCo(pAbc, pObjCo, j)
  { 
    std::vector<int> v_p;
    std::vector<int> v_n;
    std::vector<int> v_b;
    //Abc_Ntk_t* pNtk = Abc_NtkCreateCone(pAbc, Abc_ObjFanin0(pObjCo), Abc_ObjName(pObjCo), 0 );
    Abc_Ntk_t* pNtk = pAbc;
    //std::vector<char> v_ntk;
    //v_ntk = pNtk->vPis;
    Aig_Man_t* pMan = Abc_NtkToDar(pNtk,0,0);
    Cnf_Dat_t* pCnf = Cnf_Derive(pMan, Aig_ManCoNum(pMan));
    Cnf_Dat_t* pCnf_dup = Cnf_DataDup(pCnf);
    Cnf_DataLift(pCnf_dup, pCnf->nVars);

    //initilize sat solver
    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars(pSat, (pCnf->nVars) + (pCnf_dup->nVars));

    for ( int i = 0; i < pCnf->nClauses; i++ )
      {
          if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
          {
              sat_solver_delete( pSat );
          }
      }

    for ( int i = 0; i < pCnf_dup->nClauses; i++ )
      {
          if ( !sat_solver_addclause( pSat, pCnf_dup->pClauses[i], pCnf_dup->pClauses[i+1] ) )
          {
              sat_solver_delete( pSat );
          }
      }

    int numPi = Aig_ManCiNum(pMan);
    lit as [numPi + 4];
    int alpha[numPi];

    int i;
    Aig_Obj_t* pObjCi;
    Aig_ManForEachCi(pMan, pObjCi, i){
      alpha[i] = sat_solver_addvar(pSat);
      sat_solver_add_buffer_enable(pSat, pCnf->pVarNums[Aig_ObjId(pObjCi)], pCnf_dup->pVarNums[Aig_ObjId(pObjCi)], alpha[i], 0 );
      
    }
    int l;
    Aig_ManForEachCi(pMan, pObjCi, l){
      int k;
      Aig_Obj_t* pObjCij;

      Aig_ManForEachCi(pMan, pObjCij, k){
        if (l == k){
          as[k+4] = toLitCond(alpha[k], 1);
        }
        else{
          as[k+4] = toLitCond(alpha[k], 0);
        }
      }
      int n;
      int p;
      //posunate
      as[0] = toLitCond(pCnf->pVarNums[Aig_ObjId(pObjCi)], 0);
      as[1] = toLitCond(pCnf_dup->pVarNums[Aig_ObjId(pObjCi)], 1);
      as[2] = toLitCond(pCnf->pVarNums[Aig_ObjId(Aig_ManCo(pMan, j))], 0);
      as[3] = toLitCond(pCnf_dup->pVarNums[Aig_ObjId(Aig_ManCo(pMan, j))], 1);

      //if (Abc_ObjFaninC0(pObjCo) == true){
      //  n = sat_solver_solve(pSat,as ,as + numPi + 4 ,0 ,0 ,0 ,0);
      //}
      //else{
      p = sat_solver_solve(pSat,as ,as + numPi + 4 ,0 ,0 ,0 ,0);
      //}
      //negunate
      as[0] = toLitCond(pCnf->pVarNums[Aig_ObjId(pObjCi)], 1);
      as[1] = toLitCond(pCnf_dup->pVarNums[Aig_ObjId(pObjCi)], 0);
      as[2] = toLitCond(pCnf->pVarNums[Aig_ObjId(Aig_ManCo(pMan, j))], 0);
      as[3] = toLitCond(pCnf_dup->pVarNums[Aig_ObjId(Aig_ManCo(pMan, j))], 1);
      
      //if (Abc_ObjFaninC0(pObjCo) == true){
      //  p = sat_solver_solve(pSat,as ,as + numPi + 4 ,0 ,0 ,0 ,0);
      //}
      //else{
      n = sat_solver_solve(pSat,as ,as + numPi + 4 ,0 ,0 ,0 ,0);
      //}

      if (n < 0 or p < 0){
        if (n < 0){
          v_p.push_back(l);
        }
        if(p < 0){
          v_n.push_back(l);
        }
      }
      else{
        v_b.push_back(l);
      }
    }    

    printf("node %s : \n", Abc_ObjName(pObjCo));
    if (v_p.empty() != true){
      printf("+unate inputs: ");
      
      for (int i=0; i < v_p.size(); i++){
        if (i == 0){
          printf("%s", Abc_ObjName(Abc_NtkPi(pNtk, v_p[i])));
        }
        else {
          printf(",%s", Abc_ObjName(Abc_NtkPi(pNtk, v_p[i])));
        }
      }
      printf("\n");

    }
    if (v_n.empty() != true){
      
      printf("-unate inputs: ");
      
      for (int i=0; i < v_n.size(); i++){
        if (i == 0){
          printf("%s", Abc_ObjName(Abc_NtkPi(pNtk, v_n[i])));
        }
        else {
          printf(",%s", Abc_ObjName(Abc_NtkPi(pNtk, v_n[i])));
        }
      }
      printf("\n");
    }
    if (v_b.empty() != true){
      printf("binate inputs: ");
      for (int i=0; i < v_b.size(); i++){
        if (i == 0){
          printf("%s", Abc_ObjName(Abc_NtkPi(pNtk, v_b[i])));
        }
        else {
          printf(",%s", Abc_ObjName(Abc_NtkPi(pNtk, v_b[i])));
        }
      }
      printf("\n");
    }

    v_p.clear();
    v_n.clear();
    v_b.clear();
  
  }
  /*int c;
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
  return 1;*/
  return 0;
}