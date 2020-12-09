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
	// start the SAT solver
    // pSat = sat_solver_new();
	// sat_solver_addclause
	
	// add clauses for this CNF
    // Cnf_CnfForClause( pCnf, pBeg, pEnd, i )
	// if ( !sat_solver_addclause( pSat, pBeg, pEnd ) ){
		// assert( 0 ); // if it happens, can return 1 (unsatisfiable)
		// return 1;
	// }
	
	// pAig = Abc_NtkToDar(pNtk, 0, 0);
	// Abc_NtkForEachPo(pNtk, pObj, i){
		// aigPo = Aig_ManCo( pAig, i );
	// }
	// Aig_ManFlipFirstPo
	Abc_NtkForEachPi(pNtk, pObj, i){
		NtkID[i] = Abc_ObjId(pObj);
	}

	pAig = Abc_NtkToDar(pNtk, 0, 0);
	Abc_NtkForEachPo(pNtk, Po, i){
		// complement = Abc_ObjFaninC0(pObj);
		// complement = 1;
		Abc_NtkForEachPi(pNtk, pObj, j){
			protocol[j] = 0;
		}
		// printf("Object Id = %d, name = %s\n", Abc_ObjId(pFanin), Abc_ObjName(pFanin));
		pNode = Abc_NtkFindNode( pNtk, Abc_ObjName(Po) );
		// complement ^= Abc_ObjIsComplement(pObj);
		// printf("\n\nObject Id = %d, pNode name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
		// printf("\n\nNewPo Id = %d, pNode name = %s\n", Abc_ObjId(pNode), Abc_ObjName(pNode));
		// Abc_NodeComplement(pNode);
		// if(Abc_ObjIsComplement(pObj)){
			// printf("C ");
		// }else{
			// printf("N-C ");
		// }
		// printf("%d\n", Abc_ObjIsComplement(pObj));
		// Abc_NodeComplement(pObj);
		// Aig_Not( Aig_Obj_t * p ) 
		// negNtk = posNtk = Abc_NtkCreateCone(pNtk, pNode, Abc_ObjName(pNode), 0);
		// pAigNode = Aig_ManCo( pAig, i );
		// if(Aig_ObjPhase(pAigNode)){
			// printf("1\n");
		// }else{
			// printf("0\n");
		// }
		// complement ^= Aig_ObjPhase(pAigNode);
		posNtk = Abc_NtkCreateCone(pNtk, pNode, Abc_ObjName(pNode), 0);
		Abc_NtkForEachPi(posNtk, pObj, j){
			Abc_NtkForEachPi(pNtk, pObj2, k){
				if(!strcmp(Abc_ObjName(pObj), Abc_ObjName(pObj2))){
				// if(Abc_ObjName(pObj) == Abc_ObjName(pObj2)){
					map[Abc_ObjId(pObj)] = k;
					// map[j] = k;
					// printf("Abc_ObjId %d\n ", Abc_ObjId(pObj));
				}
			}
		}
		// for(){
			// for(){
				
			// }
		// }
		// printf("pAigNode Object Id = %d, name = %s\n", Abc_ObjId(pAigNode), Abc_ObjName(pAigNode));
		
		// printf("\n\nObject Id = %d, pNode name = %s\n", Abc_ObjId(pNode), Abc_ObjName(pNode));
		// printf("\n\nObject Id = %d, pNode name = %s\n", Abc_ObjId(pObj2), Abc_ObjName(pObj2));
		// Abc_NtkForEachPo(posNtk, pObj2, k){
		// }
		
		// Abc_NtkForEachNode(posNtk, pObj2, k) {
			// printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj2), Abc_ObjName(pObj2));
			// Abc_Obj_t* pFanin;
			// Abc_ObjForEachFanin(pObj2, pFanin, m) {
				// printf("	Fanin-%d: Id = %d, name = %s\n", m, Abc_ObjId(pFanin), Abc_ObjName(pFanin));
			// }
		// }
		
		// Abc_NtkForEachPi(posNtk, pObj2, k){
			// printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj2), Abc_ObjName(pObj2));
		// }
		
		pMan = Abc_NtkToDar(posNtk, 0, 0);
		if(Abc_ObjFaninC0(Po)){
			Aig_ManFlipFirstPo(pMan);
		}
		// pAigNode = Aig_ManCo( pMan, 0 );
		// if(Aig_ObjPhase(pAigNode)){
			// printf("1\n");
		// }else{
			// printf("0\n");
		// }
		
		pCnf = Cnf_Derive(pMan, 1);
		pCnf2 = Cnf_DataDup(pCnf);
		Cnf_DataLift(pCnf2, pCnf->nVars);
		// printf("=================\n");
		// Cnf_DataPrint(pCnf, 1);
		// printf("=================\n");
		// Cnf_DataPrint(pCnf2, 1);
		// printf("=================\n");
		pSat = (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0);
		Cnf_CnfForClause( pCnf2, pBeg, pEnd, k )
			sat_solver_addclause( pSat, pBeg, pEnd );
		
		// sat_solver_setnvars(pSat, Aig_ManCiNum(pMan));
		for( j = 0; j < Aig_ManCiNum(pMan); j++ ){
			m = sat_solver_addvar(pSat);
			pAigNode = Aig_ManCi( pMan, j );
			// printf("m %d\n", m);
			// printf("pCnf->pVarNums[Aig_ObjId(pAigNode) %d\n", pCnf->pVarNums[Aig_ObjId(pAigNode)]);
			// printf("pCnf2->pVarNums[Aig_ObjId(pAigNode) %d\n", pCnf2->pVarNums[Aig_ObjId(pAigNode)]);
			sat_solver_add_buffer_enable(pSat, pCnf->pVarNums[Aig_ObjId(pAigNode)],
								pCnf2->pVarNums[Aig_ObjId(pAigNode)], m, 0);
		}
		
		// for(k=0;k<2;k++){
			// pAigNode = Aig_ManCo( pMan, 0 );
			// Lits[0] = pCnf->pVarNums[Aig_ObjId(pAigNode)] + k;
			// Lits[1] = pCnf->pVarNums[Aig_ObjId(pAigNode)] + pCnf->nVars + k^1;
			// for(j=){
				// toLitCond
				// sat_solver_solve(pSat, pLit, pLit, 0, 0, 0, 0);
			// }
		// }
		pAigNode = Aig_ManCo( pMan, 0 );
		Lits[0] = toLitCond(pCnf->pVarNums[Aig_ObjId(pAigNode)], 0);
		Lits[1] = toLitCond(pCnf2->pVarNums[Aig_ObjId(pAigNode)], 1);
		// printf("HERE\n");
		for(p = 0; p < 2; p++){
			for(j = 0; j < Aig_ManCiNum(pMan); j++){
				pAigNode = Aig_ManCi( pMan, j );
				// printf("how do you look like. %d\n", j + pCnf->nVars*2);
				// printf("how do you look like. %d\n", pCnf->pVarNums[Aig_ObjId(pAigNode)]);
				// printf("how do you look like. %d\n", pCnf2->pVarNums[Aig_ObjId(pAigNode)]);
				Lits[2] = toLitCond(j + pCnf->nVars*2, 1);
				Lits[3] = toLitCond(pCnf->pVarNums[Aig_ObjId(pAigNode)], 1^p);
				Lits[4] = toLitCond(pCnf2->pVarNums[Aig_ObjId(pAigNode)], p);
				o = 5;
				for(k = 0; k < Aig_ManCiNum(pMan); k++){
					if(k != j){
						// pAigNode = Aig_ManCi( pMan, k );
						Lits[o] = toLitCond(k + pCnf->nVars*2, 0);
						// printf("who will shut down. %d\n", k + pCnf->nVars*2);
						// printf("who will shut down. %d\n", k + pCnf->nVars*2);
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
				// printf("%d ", sat_solver_solve(pSat, Lits, Lits + Aig_ManCiNum(pMan) + 4, 0, 0, 0, 0));
				// printf("pAigNode %d ", Aig_ObjId(pAigNode));
				// printf("map %d\n ", map[Aig_ObjId(pAigNode)]);
				// if(!sat_solver_solve(pSat, Lits, Lits + pCnf->nVars + 4, 0, 0, 0, 0)){
					// printf("%d");
				// }else{
					// printf("%s", );
				// }
			}
		}
		// printf("\n");
		
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
					// printf("%s ", Abc_ObjName(pObj));
					first = 0;
				}else{
					printf(",%s", Abc_ObjName(pObj));
				}
				// printf("%d ", protocol[j]);
			}
		}
		if(!first){
			printf("\n");
		}
		
		first = 1;
		// poFirst = 1;
		Abc_NtkForEachPi(pNtk, pObj, j){
			if(protocol[j] == 0 || protocol[j] == 2 || protocol[j] == 3){
				if(poFirst){
					printf("node %s: \n", Abc_ObjName(Po));
					poFirst = 0;
				}
				if(first){
					printf("-unate inputs: ");
					printf("%s", Abc_ObjName(pObj));
					// printf("%s ", Abc_ObjName(pObj));
					first = 0;
				}else{
					printf(",%s", Abc_ObjName(pObj));
				}
				// printf("%s ", Abc_ObjName(pObj));
				// printf("%d ", protocol[j]);
			}
		}
		if(!first){
			printf("\n");
		}
		
		first = 1;
		// poFirst = 1;
		Abc_NtkForEachPi(pNtk, pObj, j){
			if(protocol[j] == 5){
				if(poFirst){
					printf("node %s: \n", Abc_ObjName(Po));
					poFirst = 0;
				}
				if(first){
					printf("binate inputs: ");
					printf("%s", Abc_ObjName(pObj));
					// printf("%s ", Abc_ObjName(pObj));
					first = 0;
				}else{
					printf(",%s", Abc_ObjName(pObj));
				}
				// printf("%s ", Abc_ObjName(pObj));
				// printf("%d ", protocol[j]);
			}
		}
		if(!first){
			printf("\n");
		}
		// Aig_ObjId(pAigNode);
		// printf("Object Id = %d, var = %d\n", Aig_ObjId(pAigNode), pCnf->pVarNums[Aig_ObjId(pAigNode)]);
		// printf("Object Id = %d, var = %d\n", Aig_ObjId(pAigNode), pCnf->pVarNums[Aig_ObjId(pAigNode)] + pCnf->nVars);
		// printf("Object Id = %d\n", Aig_ObjId(pAigNode));
		// printf("pCnf nVars = %d\n", pCnf->nVars);
		// printf("pCnf nLiterals = %d\n", pCnf->nLiterals);
		// printf("pCnf nClauses = %d\n", pCnf->nClauses);
		// Cnf_CnfForClause(pCnf, pBeg, pEnd, k){
			// printf("%d ", *pBeg);
			// printf("%d\n", *pEnd);
		// }
		// printf("pCnf pVarNums = %d\n", *(pCnf->pVarNums));
		// printf("pCnf pClaPols = %s\n", pCnf->pClaPols);
		// printf("=================\n");
		// Cnf_DataPrint(pCnf, 1);
		// printf("=================\n");
		// Cnf_DataPrint(pCnf2, 1);
		// printf("=================\n");
		// printf("Object Id = %d, name = %s, var = %d\n", Abc_ObjId(pObj2), Abc_ObjName(pObj2), pCnf->pVarNums[Abc_ObjId(pObj2)]);
		// for ( k = 0; k < pCnf->nClauses; k++ )
		// {
			// if ( !sat_solver_addclause( pSat, p->pClauses[k], p->pClauses[k+1] ) )
			// {
				// sat_solver_delete( pSat );
				// return NULL;
			// }
		// }
		// Cnf_CnfForClause( pCnf, pBeg, pEnd, k )
			// sat_solver_addclause( pSat, pBeg, pEnd );
			
		// for ( k = 0; k < pCnf->nClauses; k++ ){
			// for ( pLit = pCnf->pClauses[k], pStop = pCnf->pClauses[k+1]; pLit < pStop; pLit++ )
				// fprintf( pFile, "%s%d ", Abc_LitIsCompl(*pLit) ? "-":"", fReadable? Abc_Lit2Var(*pLit) : Abc_Lit2Var(*pLit)+1 );
			// fprintf( pFile, "\n" );
		// }
		
// Abc_NtkForEachPi(posNtk, pObj2, k){
	// printf("Object Id = %d, name = %s, var = %d\n", Abc_ObjId(pObj2), Abc_ObjName(pObj2), pCnf->pVarNums[Abc_ObjId(pObj2)]);
// }
// printf("\n");		
// Abc_NtkForEachNode(posNtk, pObj2, k){
	// printf("Object Id = %d, name = %s, var = %d\n", Abc_ObjId(pObj2), Abc_ObjName(pObj2), pCnf->pVarNums[Abc_ObjId(pObj2)]);
// }
// printf("\n");		
// Abc_NtkForEachPo(posNtk, pObj2, k){
	// printf("Object Id = %d, name = %s, var = %d\n", Abc_ObjId(pObj2), Abc_ObjName(pObj2), pCnf->pVarNums[Abc_ObjId(pObj2)]);
// }
		
		//------------------------------------
		
		// Abc_NodeComplement(Abc_ObjFanin(Abc_NtkPo(negNtk, 0), 0));
		// Abc_NtkForEachPo( pNtk, pObj2, i )
			// Abc_NodeComplement(pObj2);
		// negNtk = Abc_NtkCreateCone(pNtk, pFanin, Abc_ObjName(pFanin), 0);
		// pMan = Abc_NtkToDar(negNtk, 0, 0);
		// pCnf = Cnf_Derive(pMan, 1);
		// printf("pCnf nVars = %d\n", pCnf->nVars);
		// printf("pCnf nLiterals = %d\n", pCnf->nLiterals);
		// printf("pCnf nClauses = %d\n", pCnf->nClauses);
		// Cnf_CnfForClause(pCnf, pBeg, pEnd, k){
			// printf("%d ", *pBeg);
			// printf("%d\n", *pEnd);
		// }
		// printf("pCnf pVarNums = %d\n", *(pCnf->pVarNums));
		// printf("pCnf pClaPols = %s\n", pCnf->pClaPols);
		// Cnf_DataPrint(pCnf, 1);
		// printf("=================\n");			
		// Cnf_DataPrint(pCnf, 0);
		
		//-------------------------------------
		// printf("pCnf pObj2Clause = %d\n", *(pCnf->pObj2Clause));
		// printf("pCnf pObj2Count = %d\n", *(pCnf->pObj2Count));
		// break;
			// if(pCnf->pVarNums[k] == -1) continue;
			// for(m = 0; m < pCnf->pVarNums[k]; m++){
			// printf("%d\n", *pBeg);
			// }
			// printf("\n");
			// for(m = pBeg[k], m < pEnd[], l++){
				// printf("p->pClauses = %d", *pBeg);				
			// }
			// }
		// break;
	}
  
  // Abc_NtkCreateCone
  // Abc_NtkForEachNode(pNtk, pObj, i) {
    // printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    // Abc_Obj_t* pFanin;
    // int j;
    // Abc_ObjForEachFanin(pObj, pFanin, j) {
      // printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             // Abc_ObjName(pFanin));
    // }
    // if (Abc_NtkHasSop(pNtk)) {
      // printf("The SOP of this node:\n%s", (char*)pObj->pData);
    // }
  // }
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