#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include <vector>
#include <algorithm>
#include <string>

extern "C" {
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t* pNtk, int fExors, int fRegisters );
    extern Cnf_Dat_t * Cnf_Derive( Aig_Man_t * pAig, int nOutputs );
    extern void        Cnf_DataPrint( Cnf_Dat_t * p, int fReadable );
    extern Cnf_Dat_t * Cnf_DataDup( Cnf_Dat_t * p );
    extern void        Cnf_DataLift( Cnf_Dat_t * p, int nVarsPlus );
    extern void * Cnf_DataWriteIntoSolver( Cnf_Dat_t * p, int nFrames, int fInit );
    extern lit   toLitCond(int v, int c);
    extern int sat_solver_add_buffer_enable( sat_solver * pSat, int iVarA, int iVarB, int iVarEn, int fCompl );
    extern void sat_solver_setnvars(sat_solver* s,int n);
    extern Abc_Ntk_t * Abc_NtkCreateCone( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, char * pNodeName, int fUseAllCis );
    extern ABC_DLL Abc_Obj_t * Abc_NtkFindCi( Abc_Ntk_t * pNtk, char * pName );
    extern Aig_Obj_t *  Aig_ManCo( Aig_Man_t * p, int i );
    extern void sat_solver_delete(sat_solver* s);
    extern void Cnf_DataFree( Cnf_Dat_t * p );
}

namespace {

//extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

bool Fanin_idxcmp (Abc_Obj_t i, Abc_Obj_t j) { return (i.Id < j.Id); }


static int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPounate, 0);
}

void destroy(Abc_Frame_t* pAbc){};

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager2 {
  PackageRegistrationManager2() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager2;

void Lsv_NtkPrintPounate(Abc_Ntk_t* pNtk) {
  int i, j, k;
  int nofvar;               // number of variable without alpha
  int pos_po, pos_pi;       // PI variable ID
  int neg_po, neg_pi;       // PO variable ID
  int en_var;               // en variable ID
  int unateness;            // 0 for dash ; 1 for positive unate ; 2 for negative unate ; 3 for binate
  lbool status;
  int entry;
  int IsComplement;
  int cone_idx = 0;
  Abc_Obj_t * Abc_Obj;


  Abc_NtkForEachPo( pNtk, Abc_Obj, i) {               // for each PO of the network
    Abc_Ntk_t* pCone;
    Abc_Obj_t * Abc_pObj;
    Abc_Obj_t * Abc_cObj;
    Aig_Man_t * pMan;
    Cnf_Dat_t * pCnf_pos;
    Cnf_Dat_t * pCnf_neg;
    Aig_Obj_t * Aig_PIObj;   //PI;
    Aig_Obj_t * Aig_POObj;   //PO;
    Vec_Int_t * vLits;
    std::vector<Abc_Obj_t> pos_vector;
    std::vector<Abc_Obj_t> neg_vector;           
    std::vector<Abc_Obj_t> bi_vector;    
    sat_solver* pSat;
    int *coneID;
    int maxID;
    int PI_idx;
    int eflag[4] = {0};
    cone_idx = 0;
    PI_idx = 0;

    IsComplement = Abc_ObjFaninC0(Abc_Obj);
    pCone = Abc_NtkCreateCone( pNtk, Abc_ObjFanin0(Abc_Obj), Abc_ObjName(Abc_Obj), 0 );
    coneID = new int [Vec_PtrSize(pCone->vPis)];
    maxID = Vec_PtrSize(pCone->vPis) - 1;

    Abc_NtkForEachPi( pCone, Abc_pObj, k) {
        Abc_cObj = Abc_NtkFindCi(  pNtk, Abc_ObjName(Abc_pObj) );
        coneID[cone_idx] = Abc_cObj->Id;
        cone_idx++;
    }

    pMan = Abc_NtkToDar( pCone, 0, 0 );
    pCnf_pos = Cnf_Derive( pMan,  Aig_ManCoNum(pMan));
    pCnf_neg = Cnf_DataDup(pCnf_pos);
    Cnf_DataLift( pCnf_neg, pCnf_neg->nVars );
    pSat = (sat_solver *) Cnf_DataWriteIntoSolver( pCnf_pos, 1, 0 );
    sat_solver_setnvars(pSat,  2 * pSat->size );
    for (int k = 0; k < pCnf_neg->nClauses; k++ ){
      if ( !sat_solver_addclause( pSat, pCnf_neg->pClauses[k], pCnf_neg->pClauses[k+1] ) )
        assert(0);
    }
    nofvar = pSat->size;
    sat_solver_setnvars(pSat,  pSat->size + Aig_ManCiNum(pCnf_pos->pMan));
    // add enable clause (2 clause)
    Aig_ManForEachCi( pCnf_pos->pMan, Aig_PIObj, k ) {
        pos_pi = pCnf_pos->pVarNums[Aig_PIObj->Id];
        neg_pi = pCnf_neg->pVarNums[Aig_PIObj->Id];
        en_var = k + nofvar + 1;
        sat_solver_add_buffer_enable( pSat, pos_pi, neg_pi, en_var, 0 );
    }
    vLits = Vec_IntAlloc( pCnf_pos->nVars );
    eflag[0] =  Aig_ManCiNum(pCnf_pos->pMan);
    eflag[1] = 0; 
    eflag[2] = 0;
    eflag[3] = 0;
    Aig_POObj = Aig_ManCo(pCnf_pos->pMan, 0);
    pos_po = pCnf_pos->pVarNums[Aig_POObj->Id];
    neg_po = pCnf_neg->pVarNums[Aig_POObj->Id]; 

    Aig_ManForEachCi( pCnf_pos->pMan, Aig_PIObj, j ) {            // check unateness of each PI
        unateness = 0;      
        pos_pi = pCnf_pos->pVarNums[Aig_PIObj->Id];
        neg_pi = pCnf_neg->pVarNums[Aig_PIObj->Id];

        // check positive unate 
        Vec_IntPush( vLits, toLitCond(pos_po, 0));                      // Fx 
        Vec_IntPush( vLits, toLitCond(neg_po, 1));                      // F~x
        for (k = 0; k < Aig_ManCiNum(pCnf_pos->pMan); k++) {
            en_var = k + nofvar + 1;
            if (k == j) Vec_IntPush( vLits, toLitCond(en_var, 1));      // en_var = 0
            else Vec_IntPush( vLits, toLitCond(en_var, 0));             // en_var = 1
        }   

        Vec_IntPush( vLits, toLitCond(pos_pi, 0));                      // x = 1
        Vec_IntPush( vLits, toLitCond(neg_pi, 1));                      // ~x = 0

        status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        if (status ==  l_True) {
            eflag[0]--;
            if (IsComplement) {
                eflag[2]++;
                unateness = 2;
            } else {
                eflag[1]++;
                unateness = 1;
            }
        }
        // check negative unate 
        Vec_IntRemove(vLits,  toLitCond(pos_po, 0));                     // remove constraint Fx
        Vec_IntRemove(vLits,  toLitCond(neg_po, 1));                     // remove constraint F~x
        Vec_IntPush( vLits, toLitCond(pos_po, 1));                       // Fx 
        Vec_IntPush( vLits, toLitCond(neg_po, 0));                       // F~x 
     
        status = sat_solver_solve( pSat, Vec_IntArray(vLits), Vec_IntArray(vLits) + Vec_IntSize(vLits), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
        if (status == l_True) {
            if (IsComplement) {
                if (unateness == 0) {
                    unateness = 1;
                    eflag[0]--;
                    eflag[1]++;
                }
                else if (unateness == 2) { 
                    unateness = 3;
                    eflag[2]--;
                    eflag[3]++;
                }
            } else {
                if (unateness == 0) {
                    unateness = 2;
                    eflag[0]--;
                    eflag[2]++;
                }
                else if (unateness == 1) { 
                    unateness = 3;
                    eflag[1]--;
                    eflag[3]++;
                }
            }
        }

        Abc_cObj = Abc_NtkPi( pNtk,  coneID[j] - 1 );
        if (unateness == 0) {
            pos_vector.push_back(*Abc_cObj);
            neg_vector.push_back(*Abc_cObj);
        } else if (unateness == 1) {
            pos_vector.push_back(*Abc_cObj);
        } else if (unateness == 2) {
            neg_vector.push_back(*Abc_cObj);
        } else {
            bi_vector.push_back(*Abc_cObj);
        }
        Vec_IntClear( vLits );
    }
    Abc_NtkForEachPi( pNtk, Abc_pObj, k) {
        if ((coneID[PI_idx] - 1) != k) {
            eflag[0]++;
            pos_vector.push_back(*Abc_pObj);
            neg_vector.push_back(*Abc_pObj);        
        }
        else if (PI_idx < maxID){
            PI_idx++;
        }
    }
    
    printf("node %s:\n", Abc_ObjName(Abc_NtkPo( pNtk,  i )));
    
    if (eflag[1] != 0 || eflag[0] != 0) {     
        std::sort(pos_vector.begin(), pos_vector.end(), Fanin_idxcmp); 
        printf("+unate inputs: ");
        for (int it = 0; it < pos_vector.size(); ++it) {
            Abc_cObj = &pos_vector[it];
            if (it == 0) printf("%s", Abc_ObjName(Abc_cObj));
            else printf(",%s", Abc_ObjName(Abc_cObj));
        }
        printf("\n");
    }
    if (eflag[2] != 0 || eflag[0] != 0) {     
        std::sort(neg_vector.begin(), neg_vector.end(), Fanin_idxcmp); 
        printf("-unate inputs: ");
        for (int it = 0; it < neg_vector.size(); ++it) {
            Abc_cObj = &neg_vector[it];
            if (it == 0) printf("%s", Abc_ObjName(Abc_cObj));
            else printf(",%s", Abc_ObjName(Abc_cObj));
        }
        printf("\n");
    }                                
    if (eflag[3] != 0 ) {     
        std::sort(bi_vector.begin(), bi_vector.end(), Fanin_idxcmp); 
        printf("binate inputs: ");
        for (int it = 0; it < bi_vector.size(); ++it) {
            Abc_cObj = &bi_vector[it];
            if (it == 0) printf("%s", Abc_ObjName(Abc_cObj));
            else printf(",%s", Abc_ObjName(Abc_cObj));
        }
        printf("\n");
    }    
    sat_solver_delete(pSat); 
    Cnf_DataFree(pCnf_pos);
    Cnf_DataFree(pCnf_neg);

  }
}

int Lsv_CommandPrintPounate(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintPounate(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_pounate [-h]\n");
  Abc_Print(-2, "\t        prints the po unate in the aig network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
}
