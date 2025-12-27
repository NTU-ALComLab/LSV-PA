#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"


#include <iostream> 
#include <set>      
#include <string>   
#include <map>   
#include <vector>   
#include <algorithm>

extern "C" {
    Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintmocuts(Abc_Frame_t* pAbc, int argc, char** argv);

static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static void CheckUnateness(DdManager* dd, DdNode* func, int varIdx, int nPis);
static void PrintBinatePatterns(DdManager* dd, DdNode* posWitness, DdNode* negWitness, int varIdx, int nPis);
static void ExtractPattern(DdManager* dd, DdNode* bdd, int* pattern, int varIdx, int nPis);
static void PrintPattern(const int* pattern, int nPis);

static int  Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);
static void Sat_CheckUnateness(Abc_Ntk_t* pNtk,int k,int i);
static void Sat_ExtractPattern(Abc_Ntk_t* pNtk,Cnf_Dat_t* pCnfA,sat_solver* pSat,const std::vector<int>& vPiVarA,int skipPi,std::vector<int>& pattern);


void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_printmocuts", Lsv_CommandPrintmocuts, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

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

void Lsv_NtkPrintmocuts (Abc_Ntk_t* pNtk,int k,int l);

int Lsv_CommandPrintmocuts(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  int k, l;
  int argIndex = 1;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (argc - argIndex < 2) {
    Abc_Print(-1, "Error: missing parameters <k> and <l>.\n");
    goto usage;
  }

  k = atoi(argv[argIndex]);
  l = atoi(argv[argIndex + 1]);

  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintmocuts(pNtk,k,l);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_printmocuts [-h] <k> <l>\n");
  Abc_Print(-2, "\t<k> <l>        prints k-l-feasible cuts\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

void Lsv_NtkPrintmocuts (Abc_Ntk_t* pNtk,int k,int l){

  //nodes mapped with their k-feasible cuts 
  std::map<int,std::vector<std::set<int>>> nodes_cuts;
  //cuts mapped with their supported nodes
  std::map<std::set<int>,std::set<int>> cuts_supported_nodes;
  Abc_Obj_t* pObj;
  int i;
  std::set<int> new_cut;
  
  //iterate over all objects in topological order
  Abc_NtkForEachObj(pNtk,pObj,i){

    new_cut.clear();
    int node_id = Abc_ObjId(pObj);

    
    if(Abc_ObjIsPi(pObj)){
      
      //if it is a PI the only cut is himself
      new_cut.insert(node_id);
      nodes_cuts[node_id].push_back(new_cut);
      cuts_supported_nodes[new_cut].insert(node_id);

    }
    else if(Abc_ObjIsNode(pObj)){
      
      //if it is a AND node 
      //the cuts are the combination of the cuts of the fanins 
      std::vector<std::set<int>> cut_fanin0,cut_fanin1;
      int fanin0Id,fanin1Id;

      fanin0Id=Abc_ObjFaninId0(pObj);
      fanin1Id=Abc_ObjFaninId1(pObj);
      
      //get the cuts of the fanins
      cut_fanin0=nodes_cuts[fanin0Id];
      cut_fanin1=nodes_cuts[fanin1Id];
      
      //Combine every fanins cuts
      for (const auto& cut0 : cut_fanin0){
        for (const auto& cut1 : cut_fanin1){
          
          //filtering to have only cuts size < k
          if(cut0.size() + cut1.size() <= k){
            new_cut = cut0;
            new_cut.insert(cut1.begin(),cut1.end());

            //Irredundancy Check
            bool isSubset = false;
            // Iterate directly over the current node's existing cuts
            for(auto it = nodes_cuts[node_id].begin(); it != nodes_cuts[node_id].end();){
              //if a existing cut is a subset of the new_cut then we keep the existing cut and discard new_cut
              if(std::includes(new_cut.begin(), new_cut.end(), it->begin(), it->end())){
                isSubset = true;
                break;
              } 
              //if new_cut is a subset of a existing cut then we remove the existing cut and add new_cut
              else if(std::includes(it->begin(), it->end(), new_cut.begin(), new_cut.end())){
                it = nodes_cuts[node_id].erase(it); // erase returns the next iterator
                continue; // don't increment; already moved to next
                
              } 
              else{
                ++it;
              }
            }
            
            //If new_cut is not a superset of an existing cut, add it
            if (!isSubset) {
              nodes_cuts[node_id].push_back(new_cut);
              cuts_supported_nodes[new_cut].insert(node_id);
            }
          }
        }
      }

      //add the current node as cut
      new_cut.clear();
      new_cut.insert(node_id);
      nodes_cuts[node_id].push_back(new_cut);
      cuts_supported_nodes[new_cut].insert(node_id);
    }
  }

  //print the k-l-feasible nodes
  for (const auto& pair : cuts_supported_nodes) {
    if(pair.second.size()>=l){
      for(int i : pair.first){
        // printf("%d ",i);
        printf("%s ",Abc_ObjName(Abc_NtkObj(pNtk,i))); //print node names
      }
      printf(": ");
      for(int j : pair.second){
        // printf("%d ",j);
        printf("%s ",Abc_ObjName(Abc_NtkObj(pNtk,j))); //print node names
      }
      printf("\n");
    }
  }

}


static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv){

  Abc_Ntk_t* pNtk;
  DdManager* dd;
  Abc_Obj_t *pPo, *pDriver;
  DdNode* bddFunc;
  int k, i, nPis, nPos;

  if (argc != 3) {
    Abc_Print(-1, "Usage: lsv_unate_bdd <output_index> <input_index>\n");
    return 1;
  }

  k = atoi(argv[1]);
  i = atoi(argv[2]);

  // Read network
  pNtk = Abc_FrameReadNtk(pAbc);
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if (!Abc_NtkIsBddLogic(pNtk)) {
    Abc_Print(-1, "Network is not in BDD form. Please run 'collapse' first.\n");
    return 1;
  }

  nPis = Abc_NtkPiNum(pNtk);
  nPos = Abc_NtkPoNum(pNtk);

  if (k < 0 || k >= nPos) {
    Abc_Print(-1, "Output index %d out of range [0, %d).\n", k, nPos);
    return 1;
  }
  if (i < 0 || i >= nPis) {
    Abc_Print(-1, "Input index %d out of range [0, %d).\n", i, nPis);
    return 1;
  }

  // BDD manager
  dd = (DdManager*)pNtk->pManFunc;
  if (!dd) {
    Abc_Print(-1, "BDD manager not found.\n");
    return 1;
  }

  // Extract PO function
  pPo = Abc_NtkPo(pNtk, k);
  pDriver = Abc_ObjFanin0(pPo);

  if (!pDriver || !pDriver->pData) {
    Abc_Print(-1, "No BDD function for PO %d.\n", k);
    return 1;
  }

  // Correct complemented-edge handling (both PO edge and node edge)
  bddFunc = (DdNode*)pDriver->pData;
  bddFunc = Cudd_NotCond(bddFunc, Abc_ObjFaninC0(pPo));
  Cudd_Ref(bddFunc);

  // Check unateness
  CheckUnateness(dd, bddFunc, i, nPis);

  Cudd_RecursiveDeref(dd, bddFunc);
  return 0;
}


static void CheckUnateness(DdManager* dd, DdNode* func, int varIdx, int nPis){

  DdNode *var, *cofPos, *cofNeg, *xorCof;
  DdNode *posWitness, *negWitness;

  // BDD variable (no need to Ref; CUDD owns these nodes)
  var = Cudd_bddIthVar(dd, varIdx);

  // Cofactors
  cofPos = Cudd_Cofactor(dd, func, var);
  Cudd_Ref(cofPos);

  cofNeg = Cudd_Cofactor(dd, func, Cudd_Not(var));
  Cudd_Ref(cofNeg);

  // Independence check: cofPos XOR cofNeg == 0
  xorCof = Cudd_bddXor(dd, cofPos, cofNeg);
  Cudd_Ref(xorCof);

  int isIndependent = Cudd_IsConstant(xorCof) && xorCof == Cudd_ReadLogicZero(dd);
  Cudd_RecursiveDeref(dd, xorCof);

  if (isIndependent) {
    Abc_Print(1, "independent\n");
    Cudd_RecursiveDeref(dd, cofPos);
    Cudd_RecursiveDeref(dd, cofNeg);
    return;
  }

  // Witnesses
  posWitness = Cudd_bddAnd(dd, cofPos, Cudd_Not(cofNeg));
  Cudd_Ref(posWitness);

  negWitness = Cudd_bddAnd(dd, Cudd_Not(cofPos), cofNeg);
  Cudd_Ref(negWitness);

  int posEmpty = Cudd_IsConstant(posWitness) && posWitness == Cudd_ReadLogicZero(dd);
  int negEmpty = Cudd_IsConstant(negWitness) && negWitness == Cudd_ReadLogicZero(dd);

  if (negEmpty && !posEmpty) {
    Abc_Print(1, "positive unate\n");
  } 
  else if (posEmpty && !negEmpty) {
    Abc_Print(1, "negative unate\n");
  } 
  else {
    Abc_Print(1, "binate\n");
    PrintBinatePatterns(dd, posWitness, negWitness, varIdx, nPis);
  }

  Cudd_RecursiveDeref(dd, cofPos);
  Cudd_RecursiveDeref(dd, cofNeg);
  Cudd_RecursiveDeref(dd, posWitness);
  Cudd_RecursiveDeref(dd, negWitness);
}


static void PrintBinatePatterns(DdManager* dd, DdNode* posWitness, DdNode* negWitness, int varIdx, int nPis){

  int *p1 = (int*)malloc(sizeof(int) * nPis);
  int *p2 = (int*)malloc(sizeof(int) * nPis);

  ExtractPattern(dd, posWitness, p1, varIdx, nPis);
  ExtractPattern(dd, negWitness, p2, varIdx, nPis);

  PrintPattern(p1, nPis);
  PrintPattern(p2, nPis);

  free(p1);
  free(p2);
}


static void ExtractPattern(DdManager* dd, DdNode* bdd, int* pattern, int varIdx, int nPis){

  for (int i = 0; i < nPis; i++)
    pattern[i] = -1;

  if (bdd == Cudd_ReadLogicZero(dd))
    return;

  // Allocate cube array: CUDD uses chars '0','1','2'
  char* cube = (char*)malloc((nPis + 1) * sizeof(char));  
  if (!cube) return;

  // Call CUDD function (returns 1 on success, 0 on error)
  if (!Cudd_bddPickOneCube(dd, bdd, cube)) {
    free(cube);
    return;
  }

  // CUDD encoding:
  // cube[i] == 0  → xi = 0
  // cube[i] == 1  → xi = 1
  // cube[i] == 2  → xi is don't care
  for (int i = 0; i < nPis; i++) {
    if (i == varIdx)    // xi must be '-'
      continue;

    if (cube[i] == 0)
      pattern[i] = 0;
    else if (cube[i] == 1)
      pattern[i] = 1;
    else
      pattern[i] = -1;  // don't care
  }

  free(cube);
}


static void PrintPattern(const int* pattern, int nPis)
{
  for (int i = 0; i < nPis; i++) {
    if (pattern[i] == -1)
      Abc_Print(1, "-");
    else
      Abc_Print(1, "%d", pattern[i]);
  }
  Abc_Print(1, "\n");
}


static void Sat_CheckUnateness( Abc_Ntk_t* pNtk, int k, int i );

static void Sat_ExtractPattern(
  Abc_Ntk_t* pNtk,
  sat_solver* pSat,
  const std::vector<int>& vPiVarA,
  int skipPi,
  std::vector<int>& pattern
);


static int Lsv_CommandUnateSat( Abc_Frame_t* pAbc, int argc, char** argv ){

  if ( argc != 3 ) {
    Abc_Print( -1, "Usage: lsv_unate_sat <output_index> <input_index>\n" );
    return 1;
  }

  int k = atoi( argv[1] );
  int i = atoi( argv[2] );

  Abc_Ntk_t* pNtk = Abc_FrameReadNtk( pAbc );
  if ( !pNtk ) {
    Abc_Print( -1, "Empty network.\n" );
    return 1;
  }

  if ( !Abc_NtkIsStrash( pNtk ) ) {
    Abc_Print( -1, "Network is not in AIG (strash) form. Run 'strash' first.\n" );
    return 1;
  }

  int nPos = Abc_NtkPoNum( pNtk );
  int nPis = Abc_NtkPiNum( pNtk );

  if ( k < 0 || k >= nPos ) {
    Abc_Print( -1, "Output index %d is out of range [0, %d).\n", k, nPos );
    return 1;
  }
  if ( i < 0 || i >= nPis ) {
    Abc_Print( -1, "Input index %d is out of range [0, %d).\n", i, nPis );
    return 1;
  }

  Sat_CheckUnateness( pNtk, k, i );
  return 0;
}


static void Sat_CheckUnateness( Abc_Ntk_t* pNtk, int k, int i ){

  // 1. Build cone of PO k
  Abc_Obj_t* pPo   = Abc_NtkPo( pNtk, k );
  Abc_Obj_t* pRoot = Abc_ObjFanin0( pPo );
  if ( !pRoot ) {
    Abc_Print( -1, "PO %d has no fanin.\n", k );
    return;
  }

  // fUseAllCis = 1: original PIs get pCopy → cone PIs
  Abc_Ntk_t* pCone = Abc_NtkCreateCone( pNtk, pRoot, Abc_ObjName( pPo ), 1 );
  if ( !pCone ) {
    Abc_Print( -1, "Failed to create cone for PO %d.\n", k );
    return;
  }

  // 2. Convert cone to AIG
  Aig_Man_t* pAig = Abc_NtkToDar( pCone, 0, 0 );
  if ( !pAig ) {
    Abc_Print( -1, "Failed to convert cone to AIG.\n" );
    Abc_NtkDelete( pCone );
    return;
  }

  // 3. Derive CNF for two copies: A and B
  Cnf_Dat_t* pCnfA = Cnf_Derive( pAig, 1 );
  if ( !pCnfA ) {
    Abc_Print( -1, "Cnf_Derive failed (A).\n" );
    Aig_ManStop( pAig );
    Abc_NtkDelete( pCone );
    return;
  }

  Cnf_Dat_t* pCnfB = Cnf_Derive( pAig, 1 );
  if ( !pCnfB ) {
    Abc_Print( -1, "Cnf_Derive failed (B).\n" );
    Cnf_DataFree( pCnfA );
    Aig_ManStop( pAig );
    Abc_NtkDelete( pCone );
    return;
  }

  // Lift B's variables
  Cnf_DataLift( pCnfB, pCnfA->nVars );

  // 4. SAT solver and add both CNFs
  sat_solver* pSat = sat_solver_new();
  if ( !pSat ) {
    Abc_Print( -1, "sat_solver_new failed.\n" );
    Cnf_DataFree( pCnfA );
    Cnf_DataFree( pCnfB );
    Aig_ManStop( pAig );
    Abc_NtkDelete( pCone );
    return;
  }

  sat_solver_setnvars( pSat, pCnfA->nVars + pCnfB->nVars );
  Cnf_DataWriteIntoSolverInt( pSat, pCnfA, 1, 0 );
  Cnf_DataWriteIntoSolverInt( pSat, pCnfB, 1, 0 );

  // 5. Map original PIs → CNF vars for copies A and B
  int nPisOrig = Abc_NtkPiNum( pNtk );
  std::vector<int> vPiVarA( nPisOrig, -1 );
  std::vector<int> vPiVarB( nPisOrig, -1 );

  Abc_Obj_t* pPiOrig;
  int        t;

  Abc_NtkForEachPi( pNtk, pPiOrig, t )
  {
    Abc_Obj_t* pPiCone = (Abc_Obj_t*)pPiOrig->pCopy;
    if ( !pPiCone )
      continue; // this PI not in cone

    Aig_Obj_t* pCiAig = (Aig_Obj_t*)pPiCone->pCopy;
    if ( !pCiAig )
      continue;

    Aig_Obj_t* pCiReg = Aig_Regular( pCiAig );
    int        id     = Aig_ObjId( pCiReg );

    vPiVarA[t] = pCnfA->pVarNums[id];
    vPiVarB[t] = pCnfB->pVarNums[id];
  }

  // If x_i is not in the support of this cone → independent
  if ( i < 0 || i >= nPisOrig || vPiVarA[i] == -1 )
  {
    Abc_Print( 1, "independent\n" );

    // cleanup
    sat_solver_delete( pSat );
    Cnf_DataFree( pCnfA );
    Cnf_DataFree( pCnfB );
    Aig_ManStop( pAig );
    Abc_NtkDelete( pCone );

    // clear pCopy for all objects in original network
    Abc_Obj_t* pObj;
    int        id;
    Abc_NtkForEachObj( pNtk, pObj, id )
        pObj->pCopy = NULL;

    return;
  }

  // 6. Add equality constraints xA(t) == xB(t) for all t != i
  for ( t = 0; t < nPisOrig; ++t )
  {
    if ( t == i )
      continue;
    if ( vPiVarA[t] < 0 )
      continue; // PI not in cone

    int varA = vPiVarA[t];
    int varB = vPiVarB[t];
    lit lits[2];

    // (¬xA ∨ xB)
    lits[0] = toLitCond( varA, 1 );
    lits[1] = toLitCond( varB, 0 );
    sat_solver_addclause( pSat, lits, lits + 2 );

    // (xA ∨ ¬xB)
    lits[0] = toLitCond( varA, 0 );
    lits[1] = toLitCond( varB, 1 );
    sat_solver_addclause( pSat, lits, lits + 2 );
  }

  // CNF var indices for xi in copies A and B
  int varXiA = vPiVarA[i];
  int varXiB = vPiVarB[i];

  // 7. Output variable with complement handling
  Abc_Obj_t* pPoCone   = Abc_NtkPo( pCone, 0 );
  Abc_Obj_t* pRootCone = Abc_ObjFanin0( pPoCone );
  Aig_Obj_t* pRootAig  = (Aig_Obj_t*)pRootCone->pCopy; // may be complemented

  Aig_Obj_t* pRootReg  = Aig_Regular( pRootAig );
  int        idRoot    = Aig_ObjId( pRootReg );

  int varFA = pCnfA->pVarNums[idRoot];
  int varFB = pCnfB->pVarNums[idRoot];

  int compBit = Aig_IsComplement( pRootAig ) ? 1 : 0;

  // f = var XOR compBit
  // f=1 ⇔ literal (var, compBit) must be true
  // f=0 ⇔ literal (var, !compBit) must be true
  lit litFA1 = toLitCond( varFA, compBit );
  lit litFA0 = toLitCond( varFA, !compBit );
  lit litFB1 = toLitCond( varFB, compBit );
  lit litFB0 = toLitCond( varFB, !compBit );

  // 8. SAT checks for positive/negative witnesses
  // We want: same other inputs, xiA=0, xiB=1
  // positive witness: f(0) = 0, f(1) = 1
  // negative witness: f(0) = 1, f(1) = 0

  lit asmpPos[4] = {
    toLitCond( varXiA, 1 ), // xiA = 0  (¬xiA)
    toLitCond( varXiB, 0 ), // xiB = 1  ( xiB)
    litFA0,                 // f(0) = 0
    litFB1                  // f(1) = 1
  };

  lit asmpNeg[4] = {
    toLitCond( varXiA, 1 ), // xiA = 0
    toLitCond( varXiB, 0 ), // xiB = 1
    litFA1,                 // f(0) = 1
    litFB0                  // f(1) = 0
  };

  int  resPos    = sat_solver_solve( pSat, asmpPos, asmpPos + 4, 0, 0, 0, 0 );
  bool posExists = ( resPos == l_True );

  int  resNeg    = sat_solver_solve( pSat, asmpNeg, asmpNeg + 4, 0, 0, 0, 0 );
  bool negExists = ( resNeg == l_True );

  // 9. Classify unateness and, if binate, print patterns
  if ( !posExists && !negExists )
  {
    // no 0→1 and no 1→0 transitions
    Abc_Print( 1, "independent\n" );
  }
  else if ( !posExists && negExists )
  {
    // we have 0→1 somewhere, but no 1→0
    Abc_Print( 1, "positive unate\n" );
  }
  else if ( posExists && !negExists )
  {
    // we have 1→0 somewhere, but no 0→1
    Abc_Print( 1, "negative unate\n" );
  }
  else
  {
    // both exist → binate
    Abc_Print( 1, "binate\n" );

    std::vector<int> pat1( nPisOrig, -1 );
    std::vector<int> pat2( nPisOrig, -1 );

    // Pattern 1: from positive witness
    resPos = sat_solver_solve( pSat, asmpPos, asmpPos + 4, 0, 0, 0, 0 );
    if ( resPos == l_True )
        Sat_ExtractPattern( pNtk, pSat, vPiVarA, i, pat1 );

    // Pattern 2: from negative witness
    resNeg = sat_solver_solve( pSat, asmpNeg, asmpNeg + 4, 0, 0, 0, 0 );
    if ( resNeg == l_True )
      Sat_ExtractPattern( pNtk, pSat, vPiVarA, i, pat2 );

    PrintPattern( pat1.data(), nPisOrig );
    PrintPattern( pat2.data(), nPisOrig );
  }

  // 10. Cleanup
  sat_solver_delete( pSat );
  Cnf_DataFree( pCnfA );
  Cnf_DataFree( pCnfB );
  Aig_ManStop( pAig );
  Abc_NtkDelete( pCone );

  // clear pCopy for all objects in original network
  Abc_Obj_t* pObj;
  int        id;
  Abc_NtkForEachObj( pNtk, pObj, id )
      pObj->pCopy = NULL;
}



static void Sat_ExtractPattern(Abc_Ntk_t*pNtk, sat_solver* pSat,const std::vector<int>& vPiVarA,int skipPi,std::vector<int>&pattern){
  
  int nPis = Abc_NtkPiNum( pNtk );
  pattern.assign( nPis, -1 );

  for ( int t = 0; t < nPis; ++t )
  {
    if ( t == skipPi ) {
      pattern[t] = -1; // '-' for variable under test
      continue;
    }

    int varA = vPiVarA[t];
    if ( varA == -1 ) {
      // PI not in support of this PO
      pattern[t] = -1;
      continue;
    }

    int val = sat_solver_var_value( pSat, varA ); // usually 0 or 1
    pattern[t] = val ? 1 : 0;
  }
}
