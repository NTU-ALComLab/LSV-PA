#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"

// ABC_NAMESPACE_IMPL_START

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
extern "C" Cnf_Dat_t * Cnf_Derive( Aig_Man_t * pAig, int nOutputs );

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintNodes, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
	Aig_Man_t * pMan;
	Aig_Man_t * pAig;
	Aig_Obj_t * pAigNode;
	Abc_Obj_t * pObj;
	Abc_Obj_t * Po;
	Abc_Obj_t * pObj2;
	Abc_Obj_t * pNode;
	Abc_Ntk_t * posNtk;
	// Abc_Ntk_t * negNtk;
	Cnf_Dat_t * pCnf;
	Cnf_Dat_t * pCnf2;
	
	// Abc_Obj_t ** aigPo;
	int i, j, k, m, o, p;
	int * pBeg, * pEnd;
	int first, poFirst;
	
	lit Lits[99999];
	int NtkID[99999];
	int protocol[99999];
	int map[99999];
	sat_solver * pSat;
	
	Abc_NtkForEachPi(pNtk, pObj, i){
		NtkID[i] = Abc_ObjId(pObj);
	}

	pAig = Abc_NtkToDar(pNtk, 0, 0);
	Abc_NtkForEachPo(pNtk, Po, i){
		Abc_NtkForEachPi(pNtk, pObj, j){
			protocol[j] = 0;
		}
		pNode = Abc_NtkFindNode( pNtk, Abc_ObjName(Po) );
		posNtk = Abc_NtkCreateCone(pNtk, pNode, Abc_ObjName(pNode), 0);
		Abc_NtkForEachPi(posNtk, pObj, j){
			Abc_NtkForEachPi(pNtk, pObj2, k){
				if(!strcmp(Abc_ObjName(pObj), Abc_ObjName(pObj2))){
					map[Abc_ObjId(pObj)] = k;
				}
			}
		}
		
		pMan = Abc_NtkToDar(posNtk, 0, 0);
		if(Abc_ObjFaninC0(Po)){
			Aig_ManFlipFirstPo(pMan);
		}
		
		pCnf = Cnf_Derive(pMan, 1);
		pCnf2 = Cnf_DataDup(pCnf);
		Cnf_DataLift(pCnf2, pCnf->nVars);
		
		pSat = (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0);
		Cnf_CnfForClause( pCnf2, pBeg, pEnd, k )
			sat_solver_addclause( pSat, pBeg, pEnd );
			
		for( j = 0; j < Aig_ManCiNum(pMan); j++ ){
			m = sat_solver_addvar(pSat);
			pAigNode = Aig_ManCi( pMan, j );
			sat_solver_add_buffer_enable(pSat, pCnf->pVarNums[Aig_ObjId(pAigNode)],
								pCnf2->pVarNums[Aig_ObjId(pAigNode)], m, 0);
		}
		
		pAigNode = Aig_ManCo( pMan, 0 );
		Lits[0] = toLitCond(pCnf->pVarNums[Aig_ObjId(pAigNode)], 0);
		Lits[1] = toLitCond(pCnf2->pVarNums[Aig_ObjId(pAigNode)], 1);
		
		for(p = 0; p < 2; p++){
			for(j = 0; j < Aig_ManCiNum(pMan); j++){
				pAigNode = Aig_ManCi( pMan, j );
				
				Lits[2] = toLitCond(j + pCnf->nVars*2, 1);
				Lits[3] = toLitCond(pCnf->pVarNums[Aig_ObjId(pAigNode)], 1^p);
				Lits[4] = toLitCond(pCnf2->pVarNums[Aig_ObjId(pAigNode)], p);
				o = 5;
				for(k = 0; k < Aig_ManCiNum(pMan); k++){
					if(k != j){
						
						Lits[o] = toLitCond(k + pCnf->nVars*2, 0);
						o++;
					}
				}
				if(p == 0){
					if(sat_solver_solve(pSat, Lits, Lits + Aig_ManCiNum(pMan) + 4, 0, 0, 0, 0) == -1){
						protocol[map[Aig_ObjId(pAigNode)]] = 1;
					}else{
						protocol[map[Aig_ObjId(pAigNode)]] = 4;
					}
				}else{
					if(sat_solver_solve(pSat, Lits, Lits + Aig_ManCiNum(pMan) + 4, 0, 0, 0, 0) == -1){
						if(protocol[map[Aig_ObjId(pAigNode)]] == 1){							
							protocol[map[Aig_ObjId(pAigNode)]] = 3;
						}else{							
							protocol[map[Aig_ObjId(pAigNode)]] = 2;
						}
					}else{
						if(protocol[map[Aig_ObjId(pAigNode)]] == 4){
							protocol[map[Aig_ObjId(pAigNode)]] = 5;
						}
					}
				}
			}
		}
		
		first = 1;
		poFirst = 1;
		Abc_NtkForEachPi(pNtk, pObj, j){
			if(protocol[j] == 0 || protocol[j] == 1 || protocol[j] == 3){
				if(poFirst){
					printf("node %s: \n", Abc_ObjName(Po));
					poFirst = 0;
				}
				if(first){
					printf("+unate inputs: ");
					printf("%s", Abc_ObjName(pObj));
					first = 0;
				}else{
					printf(",%s", Abc_ObjName(pObj));
				}
			}
		}
		if(!first){
			printf("\n");
		}
		
		first = 1;
		Abc_NtkForEachPi(pNtk, pObj, j){
			if(protocol[j] == 0 || protocol[j] == 2 || protocol[j] == 3){
				if(poFirst){
					printf("node %s: \n", Abc_ObjName(Po));
					poFirst = 0;
				}
				if(first){
					printf("-unate inputs: ");
					printf("%s", Abc_ObjName(pObj));
					first = 0;
				}else{
					printf(",%s", Abc_ObjName(pObj));
				}
			}
		}
		if(!first){
			printf("\n");
		}
		
		first = 1;
		Abc_NtkForEachPi(pNtk, pObj, j){
			if(protocol[j] == 5){
				if(poFirst){
					printf("node %s: \n", Abc_ObjName(Po));
					poFirst = 0;
				}
				if(first){
					printf("binate inputs: ");
					printf("%s", Abc_ObjName(pObj));
					first = 0;
				}else{
					printf(",%s", Abc_ObjName(pObj));
				}
			}
		}
		if(!first){
			printf("\n");
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