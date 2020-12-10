#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include <map>
#include <string>
using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern "C" Cnf_Dat_t *Cnf_Derive(Aig_Man_t *pAig, int nOutputs);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintNodes, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t * pObj;
  Abc_Obj_t * pObj2;
  Abc_Obj_t * pObj3;
  Abc_Obj_t * pObj4;
  Abc_Obj_t * pObj5;
  Aig_Man_t * pAigMan;
  Aig_Man_t * pAig;
  Cnf_Dat_t * pcnf;
  Cnf_Dat_t * pcnf2;
  sat_solver * psat_solver;
  
  int iscomplement;
  Abc_Ntk_t* pntk;
  Abc_Obj_t * pNode;
  Aig_Obj_t * pAigNode;
  Aig_Obj_t * pAigObj;
  Abc_Obj_t * Po;

  int * pBen;
  int * pEnd;
  lit Lits[100000];
  int pro[100000];

  int n, l, p, e;
  int ans, neg_ans;
  map<int, int> id_id;
  // Abc_Ntk_t * Abc_NtkCreateCone( Abc_Ntk_t * pNtk, Abc_Obj_t * pNode, char * pNodeName, int fUseAllCis )
  int i;

  pAig = Abc_NtkToDar(pNtk, 0, 0);
  Abc_NtkForEachPo(pNtk, pObj, i) {
    
    int j;
    iscomplement = 1;
    pNode = Abc_NtkFindNode(pNtk, Abc_ObjName(pObj));
        // printf("node %s:\n", Abc_ObjName(pObj));
        
        pAigNode = Aig_ManCo(pAig, i);
        
        pntk = Abc_NtkCreateCone(pNtk, pNode, Abc_ObjName(pNode), 0);
        
        pAigMan = Abc_NtkToDar( pntk, 0, 0);

        if(Abc_ObjFaninC0(pObj)){
          Aig_ManFlipFirstPo(pAigMan);
        }
        pcnf = Cnf_Derive(pAigMan, 1);

        pcnf2 = Cnf_DataDup(pcnf);
        Cnf_DataLift(pcnf2, pcnf->nVars);

        int v, w;
        Abc_Obj_t * ntk_node;
        Abc_NtkForEachPi(pntk, ntk_node, v){
            Abc_NtkForEachPi(pNtk, pObj2, w){
              // printf("Pi name: %s\n", Abc_ObjName(ntk_node));
              // printf("orig_Pi name: %s\n", Abc_ObjName(pObj));
              string orig(Abc_ObjName(ntk_node));
              string newnode(Abc_ObjName(pObj2));
              if(orig == newnode){
                id_id[Abc_ObjId(ntk_node)] = w;
                // printf("id:%d to id:%d \n", v, Abc_ObjId(pObj));
                // printf("same!!!\n");
              }
              
            }
        }


        psat_solver = (sat_solver *)Cnf_DataWriteIntoSolver(pcnf, 1, 0);
        Cnf_CnfForClause(pcnf2, pBen, pEnd, p)
          sat_solver_addclause(psat_solver, pBen, pEnd);

        for(int k = 0; k < Aig_ManCiNum(pAigMan); k++){
          n = sat_solver_addvar(psat_solver);
          // printf("add alpha: %d\n", n);
          pAigObj = Aig_ManCi( pAigMan, k );
          int Cnf_var = pcnf->pVarNums[Aig_ObjId(pAigObj)];
          int Cnf2_var = pcnf2->pVarNums[Aig_ObjId(pAigObj)];
          sat_solver_add_buffer_enable(psat_solver, Cnf_var, Cnf2_var, n, 0);

          // printf("cnf var: %d\n", pcnf->pVarNums[Aig_ObjId(pAigObj)]);
          // printf("cnf2 var: %d\n", pcnf2->pVarNums[Aig_ObjId(pAigObj)]);

        }

        // Cnf_DataPrint(pcnf, 1);
        // printf("=======\n");
        // Cnf_DataPrint(pcnf2, 1);
        
        
        // for(int m = 0; m < 2*pcnf->nVars ; m++){
        //   printf("clause: %d\n", psat_solver->fPrintClause);
        // }

        pAigObj = Aig_ManCo( pAigMan, 0 );
        Lits[0] = toLitCond(pcnf->pVarNums[Aig_ObjId(pAigObj)], 0);
		    Lits[1] = toLitCond(pcnf2->pVarNums[Aig_ObjId(pAigObj)], 1);

        //----
        
        for(int f = 0; f < 2; f++){
          for(int j = 0; j < Aig_ManCiNum(pAigMan); j++){

            pAigNode = Aig_ManCi( pAigMan, j );


            Lits[2] = toLitCond(j + pcnf->nVars*2, 1);
            
            Lits[3] = toLitCond(pcnf->pVarNums[Aig_ObjId(pAigNode)], 1^f);
            Lits[4] = toLitCond(pcnf2->pVarNums[Aig_ObjId(pAigNode)], f);
            
            l = 5;
            for(int q = 0; q < Aig_ManCiNum(pAigMan); q++){
              if(q != j){
                Lits[l] = toLitCond(q + pcnf->nVars*2, 0);
                l++;
						
              }
            }
            
              if(f == 0){
                ans = sat_solver_solve(psat_solver, Lits, Lits + Aig_ManCiNum(pAigMan) + 4, 0, 0, 0, 0);
                if(ans == -1){
                  pro[id_id[Aig_ObjId(pAigNode)]] = 1;
                }else{
                  pro[id_id[Aig_ObjId(pAigNode)]] = 4;
                }
              }else{
                neg_ans = sat_solver_solve(psat_solver, Lits, Lits + Aig_ManCiNum(pAigMan) + 4, 0, 0, 0, 0);

                if(neg_ans == -1){
                  if(pro[id_id[Aig_ObjId(pAigNode)]] == 1){
                    pro[id_id[Aig_ObjId(pAigNode)]] = 3;
                  }else{
                    pro[id_id[Aig_ObjId(pAigNode)]] = 2;
                  }
                }else{
                  if(pro[id_id[Aig_ObjId(pAigNode)]] == 4){
                    pro[id_id[Aig_ObjId(pAigNode)]] = 5;
                  }
                }
              }
              
          }
          
        }   
        
        int ff = 1;
        int poFirst = 1;
        Abc_NtkForEachPi(pNtk, pObj3, j){
          if(pro[j] == 1 || pro[j] == 3 || pro[j] == 0){
            if(poFirst){
              printf("node %s: \n", Abc_ObjName(pObj));
              poFirst = 0;
            }
            if(ff){
              printf("+unate inputs: ");
              printf("%s", Abc_ObjName(pObj3));
              ff = 0;
            }else{
              printf(",%s", Abc_ObjName(pObj3));
            }
          }
        }
        if(!ff){
          printf("\n");
        }

        ff = 1;
        Abc_NtkForEachPi(pNtk, pObj4, j){
          if(pro[j] == 2 || pro[j] == 3 || pro[j] == 0){
            if(poFirst){
              printf("node %s: \n", Abc_ObjName(pObj));
              poFirst = 0;
            }
            if(ff){
              printf("-unate inputs: ");
              printf("%s", Abc_ObjName(pObj4));
              ff = 0;
            }else{
              printf(",%s", Abc_ObjName(pObj4));
            }
          }
        }
        if(!ff){
          printf("\n");
        }

        ff = 1;
        Abc_NtkForEachPi(pNtk, pObj5, j){
          if(poFirst){
              printf("node %s: \n", Abc_ObjName(pObj));
              poFirst = 0;
            }
          if(pro[j] == 5){
            if(ff){
              printf("binate inputs: ");
              printf("%s", Abc_ObjName(pObj5));
              ff = 0;
            }else{
              printf(",%s", Abc_ObjName(pObj5));
            }
          }
        }
        if(!ff){
          printf("\n");
        }

        Abc_NtkForEachPi(pNtk, pObj, e){
          pro[e] = 0;
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