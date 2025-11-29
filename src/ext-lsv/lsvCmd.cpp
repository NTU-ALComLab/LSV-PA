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


static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv)
{
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

    // Get network and validate
    pNtk = Abc_FrameReadNtk(pAbc);
    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }

    if (!Abc_NtkIsBddLogic(pNtk)) {
        Abc_Print(-1, "Network is not in BDD form. Please run 'collapse' first.\n");
        return 1;
    }

    // Validate indices
    nPis = Abc_NtkPiNum(pNtk);
    nPos = Abc_NtkPoNum(pNtk);

    if (k < 0 || k >= nPos) {
        Abc_Print(-1, "Output index %d is out of range [0, %d).\n", k, nPos);
        return 1;
    }

    if (i < 0 || i >= nPis) {
        Abc_Print(-1, "Input index %d is out of range [0, %d).\n", i, nPis);
        return 1;
    }

    // Get BDD manager
    dd = (DdManager*)pNtk->pManFunc;
    if (dd == NULL) {
        Abc_Print(-1, "BDD manager not found.\n");
        return 1;
    }

    // Get the k-th primary output's BDD function
    pPo = Abc_NtkPo(pNtk, k);
    pDriver = Abc_ObjFanin0(pPo);

    if (pDriver == NULL || pDriver->pData == NULL) {
        Abc_Print(-1, "BDD function not found for output %d.\n", k);
        return 1;
    }

    // Get BDD and handle complemented edge
    bddFunc = (DdNode*)pDriver->pData;
    if (Abc_ObjFaninC0(pPo)) {
        bddFunc = Cudd_Not(bddFunc);
    }
    Cudd_Ref(bddFunc);

    // Perform unateness check
    CheckUnateness(dd, bddFunc, i, nPis);

    // Cleanup
    Cudd_RecursiveDeref(dd, bddFunc);

    return 0;
}

// Core unateness checking logic
static void CheckUnateness(DdManager* dd, DdNode* func, int varIdx, int nPis)
{
    DdNode *var, *cofPos, *cofNeg, *xorCof, *posWitness, *negWitness;
    int isIndependent, isPosUnate, isNegUnate;

    // Get BDD variable for the i-th primary input
    // After collapse, PI index i corresponds to BDD variable i
    var = Cudd_bddIthVar(dd, varIdx);
    Cudd_Ref(var);

    // Compute positive cofactor f|xi=1 and negative cofactor f|xi=0
    cofPos = Cudd_Cofactor(dd, func, var);
    Cudd_Ref(cofPos);

    cofNeg = Cudd_Cofactor(dd, func, Cudd_Not(var));
    Cudd_Ref(cofNeg);

    // Check for independence: f|xi=1 == f|xi=0
    xorCof = Cudd_bddXor(dd, cofPos, cofNeg);
    Cudd_Ref(xorCof);
    isIndependent = (xorCof == Cudd_ReadLogicZero(dd));
    Cudd_RecursiveDeref(dd, xorCof);

    if (isIndependent) {
        Abc_Print(1, "independent\n");
        Cudd_RecursiveDeref(dd, var);
        Cudd_RecursiveDeref(dd, cofPos);
        Cudd_RecursiveDeref(dd, cofNeg);
        return;
    }

    // Compute witness sets
    // posWitness: assignments where f goes from 0 to 1 when xi flips 0->1
    posWitness = Cudd_bddAnd(dd, cofPos, Cudd_Not(cofNeg));
    Cudd_Ref(posWitness);

    // negWitness: assignments where f goes from 1 to 0 when xi flips 0->1
    negWitness = Cudd_bddAnd(dd, Cudd_Not(cofPos), cofNeg);
    Cudd_Ref(negWitness);

    // Check which witnesses exist
    isPosUnate = (negWitness == Cudd_ReadLogicZero(dd));
    isNegUnate = (posWitness == Cudd_ReadLogicZero(dd));

    if (isPosUnate && isNegUnate) {
        // Both empty => independent (shouldn't happen, caught above)
        Abc_Print(1, "independent\n");
    }
    else if (isPosUnate) {
        // Only positive witness exists => positive unate
        Abc_Print(1, "positive unate\n");
    }
    else if (isNegUnate) {
        // Only negative witness exists => negative unate
        Abc_Print(1, "negative unate\n");
    }
    else {
        // Both witnesses exist => binate
        Abc_Print(1, "binate\n");
        PrintBinatePatterns(dd, posWitness, negWitness, varIdx, nPis);
    }

    // Cleanup
    Cudd_RecursiveDeref(dd, var);
    Cudd_RecursiveDeref(dd, cofPos);
    Cudd_RecursiveDeref(dd, cofNeg);
    Cudd_RecursiveDeref(dd, posWitness);
    Cudd_RecursiveDeref(dd, negWitness);
}

// Find and print binate patterns
static void PrintBinatePatterns(DdManager* dd, DdNode* posWitness, DdNode* negWitness, int varIdx, int nPis)
{
    int *pattern1, *pattern2;

    // Allocate pattern arrays
    pattern1 = new int[nPis];
    pattern2 = new int[nPis];

    // Extract pattern where function behaves as xi (positive dependency)
    ExtractPattern(dd, posWitness, pattern1, varIdx, nPis);

    // Extract pattern where function behaves as !xi (negative dependency)
    ExtractPattern(dd, negWitness, pattern2, varIdx, nPis);

    // Print both patterns
    PrintPattern(pattern1, nPis);
    PrintPattern(pattern2, nPis);

    // Cleanup
    delete[] pattern1;
    delete[] pattern2;
}

// Extract a satisfying assignment from a BDD
static void ExtractPattern(DdManager* dd, DdNode* bdd, int* pattern, int varIdx, int nPis)
{
    DdNode *var, *current;
    int i;

    // Initialize pattern with don't cares
    for (i = 0; i < nPis; i++) {
        pattern[i] = -1;
    }

    // If BDD is empty, return all don't cares
    if (bdd == Cudd_ReadLogicZero(dd)) {
        return;
    }

    // Traverse the BDD to extract a satisfying path
    current = bdd;
    Cudd_Ref(current);

    for (i = 0; i < nPis; i++) {
        // Variable being checked should be don't care (printed as '-')
        if (i == varIdx) {
            pattern[i] = -1;
            continue;
        }

        var = Cudd_bddIthVar(dd, i);

        // Cofactor with positive literal (xi = 1)
        DdNode* cof1 = Cudd_Cofactor(dd, current, var);
        Cudd_Ref(cof1);

        // Cofactor with negative literal (xi = 0)
        DdNode* cof0 = Cudd_Cofactor(dd, current, Cudd_Not(var));
        Cudd_Ref(cof0);

        // Choose path based on which cofactor is non-zero
        if (cof1 != Cudd_ReadLogicZero(dd)) {
            pattern[i] = 1;
            Cudd_RecursiveDeref(dd, current);
            Cudd_RecursiveDeref(dd, cof0);
            current = cof1;
        } else if (cof0 != Cudd_ReadLogicZero(dd)) {
            pattern[i] = 0;
            Cudd_RecursiveDeref(dd, current);
            Cudd_RecursiveDeref(dd, cof1);
            current = cof0;
        } else {
            // Both are zero (shouldn't happen if bdd was non-zero)
            pattern[i] = -1;
            Cudd_RecursiveDeref(dd, cof0);
            Cudd_RecursiveDeref(dd, cof1);
        }
    }

    Cudd_RecursiveDeref(dd, current);
}

// Print pattern as a string of 0/1/-
static void PrintPattern(const int* pattern, int nPis)
{
    int i;
    for (i = 0; i < nPis; i++) {
        if (pattern[i] == -1) {
            Abc_Print(1, "-");
        } else {
            Abc_Print(1, "%d", pattern[i]);
        }
    }
    Abc_Print(1, "\n");
}

static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv)
{
    if (argc != 3) {
        Abc_Print(-1, "Usage: lsv_unate_sat <output_index> <input_index>\n");
        return 1;
    }

    int k = atoi(argv[1]);
    int i = atoi(argv[2]);

    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    if (!pNtk) {
      Abc_Print(-1, "Empty network.\n");
      return 1;
    }

    if (!Abc_NtkIsStrash(pNtk)) {
      Abc_Print(-1, "Network is not in AIG (strash) form. Run 'strash' first.\n");
      return 1;
    }

    int nPos = Abc_NtkPoNum(pNtk);
    int nPis = Abc_NtkPiNum(pNtk);

    if (k < 0 || k >= nPos) {
      Abc_Print(-1, "Output index %d is out of range [0, %d).\n", k, nPos);
      return 1;
    }
    if (i < 0 || i >= nPis) {
      Abc_Print(-1, "Input index %d is out of range [0, %d).\n", i, nPis);
      return 1;
    }

    Sat_CheckUnateness(pNtk, k, i);
    return 0;
}

// Build SAT instance for one PO/PI pair and classify unateness
static void Sat_CheckUnateness(Abc_Ntk_t* pNtk, int k, int i)
{
    // Step 1: build the cone of PO k
    Abc_Obj_t* pPo      = Abc_NtkPo(pNtk, k);
    Abc_Obj_t* pRoot    = Abc_ObjFanin0(pPo);
    if (!pRoot) {
      Abc_Print(-1, "PO %d has no fanin.\n", k);
      return;
    }

    // Include all CIs so original PIs keep a consistent mapping (.pCopy)
    Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, pRoot, Abc_ObjName(pPo), 1);
    if (!pCone) {
      Abc_Print(-1, "Failed to create cone for PO %d.\n", k);
      return;
    }

    // Step 2: convert cone to AIG (DAR)
    Aig_Man_t* pAig = Abc_NtkToDar(pCone, 0, 0);
    if (!pAig) {
      Abc_Print(-1, "Failed to convert cone to AIG.\n");
      Abc_NtkDelete(pCone);
      return;
    }

    // Step 3 & 4: derive CNF for two copies, A and B
    Cnf_Dat_t* pCnfA = Cnf_Derive(pAig, 1);  // one output cone
    if (!pCnfA) {
      Abc_Print(-1, "Cnf_Derive failed.\n");
      Aig_ManStop(pAig);
      Abc_NtkDelete(pCone);
      return;
    }

    Cnf_Dat_t* pCnfB = Cnf_Derive(pAig, 1);
    if (!pCnfB) {
      Abc_Print(-1, "Cnf_Derive failed for second copy.\n");
      Cnf_DataFree(pCnfA);
      Aig_ManStop(pAig);
      Abc_NtkDelete(pCone);
      return;
    }

    // Lift B's variables so that pCnfB uses fresh variable numbers
    Cnf_DataLift(pCnfB, pCnfA->nVars);

    // Step 5 & 6: create SAT solver and add both CNFs
    sat_solver* pSat = sat_solver_new();
    if (!pSat) {
      Abc_Print(-1, "sat_solver_new failed.\n");
      Cnf_DataFree(pCnfA);
      Cnf_DataFree(pCnfB);
      Aig_ManStop(pAig);
      Abc_NtkDelete(pCone);
      return;
    }

    // Number of variables in combined CNF
    sat_solver_setnvars(pSat, pCnfA->nVars + pCnfB->nVars);

    // Write CNF of A and B into the solver
    Cnf_DataWriteIntoSolverInt(pSat, pCnfA, 1, 0);
    Cnf_DataWriteIntoSolverInt(pSat, pCnfB, 1, 0);

    // Step 7: find CNF variables for each PI (copy A/B) and add x_t^A == x_t^B for t != i

    int nPisOrig = Abc_NtkPiNum(pNtk);
    std::vector<int> vPiVarA(nPisOrig, -1);
    std::vector<int> vPiVarB(nPisOrig, -1);

    // Map original PIs -> cone PIs -> AIG CIs -> CNF variables
    Abc_Obj_t* pPiOrig;
    int t;
    Abc_NtkForEachPi(pNtk, pPiOrig, t) {
      // pPiOrig->pCopy was set to the corresponding PI in the cone (because fUseAllCis=1)
      Abc_Obj_t* pPiCone = (Abc_Obj_t*)pPiOrig->pCopy;
      if (!pPiCone) continue;  // this PI not in the cone

      Aig_Obj_t* pCiAig = (Aig_Obj_t*)pPiCone->pCopy; // set by Abc_NtkToDar
      if (!pCiAig) continue;

      int id = Aig_ObjId(pCiAig);
      vPiVarA[t] = pCnfA->pVarNums[id];
      vPiVarB[t] = pCnfB->pVarNums[id];
    }

    // If x_i is not in the support of the cone, it's independent.
    if (i < 0 || i >= nPisOrig || vPiVarA[i] == -1) {
      Abc_Print(1, "independent\n");
      // cleanup
      sat_solver_delete(pSat);
      Cnf_DataFree(pCnfA);
      Cnf_DataFree(pCnfB);
      Aig_ManStop(pAig);
      Abc_NtkDelete(pCone);
      // reset pCopy on original PIs
      Abc_NtkForEachPi(pNtk, pPiOrig, t)
          pPiOrig->pCopy = NULL;
      return;
    }

    // Add equality constraints for all PIs except x_i:
    // vA(t) == vB(t) <=> (¬vA ∨ vB) ∧ (vA ∨ ¬vB)
    for (t = 0; t < nPisOrig; ++t) {
      if (t == i) continue;
      if (vPiVarA[t] == -1) continue; // not in cone

      int varA = vPiVarA[t];
      int varB = vPiVarB[t];

      lit lits[2];

      // (¬vA ∨ vB)
      lits[0] = toLitCond(varA, 1);
      lits[1] = toLitCond(varB, 0);
      sat_solver_addclause(pSat, lits, lits + 2);

      // (vA ∨ ¬vB)
      lits[0] = toLitCond(varA, 0);
      lits[1] = toLitCond(varB, 1);
      sat_solver_addclause(pSat, lits, lits + 2);
    }

    // CNF variables for x_i in A/B
    int varXiA = vPiVarA[i];
    int varXiB = vPiVarB[i];

    // CNF variables for output y_k in A/B
    Abc_Obj_t* pPoCone = Abc_NtkPo(pCone, 0);
    Abc_Obj_t* pRootCone = Abc_ObjFanin0(pPoCone);
    Aig_Obj_t* pRootAig = (Aig_Obj_t*)pRootCone->pCopy;
    int varFA = pCnfA->pVarNums[Aig_ObjId(pRootAig)];
    int varFB = pCnfB->pVarNums[Aig_ObjId(pRootAig)];

    // Step 8: SAT checks with assumptions
    // Positive witness: f(0) = 0, f(1) = 1  => binate or positive dependence
    // Negative witness: f(0) = 1, f(1) = 0  => binate or negative dependence

    lit asmpPos[4];
    lit asmpNeg[4];

    asmpPos[0] = toLitCond(varXiA, 1); // xiA = 0
    asmpPos[1] = toLitCond(varXiB, 0); // xiB = 1
    asmpPos[2] = toLitCond(varFA, 1);  // yA = 0
    asmpPos[3] = toLitCond(varFB, 0);  // yB = 1

    asmpNeg[0] = toLitCond(varXiA, 1); // xiA = 0
    asmpNeg[1] = toLitCond(varXiB, 0); // xiB = 1
    asmpNeg[2] = toLitCond(varFA, 0);  // yA = 1
    asmpNeg[3] = toLitCond(varFB, 1);  // yB = 0

    int resPos = sat_solver_solve(pSat, asmpPos, asmpPos + 4, 0, 0, 0, 0);
    bool posExists = (resPos == l_True);

    int resNeg = sat_solver_solve(pSat, asmpNeg, asmpNeg + 4, 0, 0, 0, 0);
    bool negExists = (resNeg == l_True);

    // Step 9: classify
    if (!posExists && !negExists) {
        Abc_Print(1, "independent\n");
    }
    else if (posExists && !negExists) {
        Abc_Print(1, "positive unate\n");
    }
    else if (!posExists && negExists) {
        Abc_Print(1, "negative unate\n");
    }
    else {
        // binate: both witnesses exist -> also print patterns

        Abc_Print(1, "binate\n");

        std::vector<int> pat1(nPisOrig, -1);
        std::vector<int> pat2(nPisOrig, -1);

        // For pat1: re-solve with positive witness assumptions to get the model
        resPos = sat_solver_solve(pSat, asmpPos, asmpPos + 4, 0, 0, 0, 0);
        if (resPos == l_True) {
            Sat_ExtractPattern(pNtk, pCnfA, pSat, vPiVarA, i, pat1);
        }
        // For pat2: solve with negative witness assumptions
        resNeg = sat_solver_solve(pSat, asmpNeg, asmpNeg + 4, 0, 0, 0, 0);
        if (resNeg == l_True) {
            Sat_ExtractPattern(pNtk, pCnfA, pSat, vPiVarA, i, pat2);
        }

        // Use your existing PrintPattern(int*, nPis) from the BDD part
        PrintPattern(pat1.data(), nPisOrig);
        PrintPattern(pat2.data(), nPisOrig);
    }

    // Cleanup
    sat_solver_delete(pSat);
    Cnf_DataFree(pCnfA);
    Cnf_DataFree(pCnfB);
    Aig_ManStop(pAig);
    Abc_NtkDelete(pCone);

    // reset pCopy on original PIs
    Abc_NtkForEachPi(pNtk, pPiOrig, t)
        pPiOrig->pCopy = NULL;
}

// Extract one satisfying PI pattern from solver model (copy A)
static void Sat_ExtractPattern(
    Abc_Ntk_t* pNtk,
    Cnf_Dat_t*,
    sat_solver* pSat,
    const std::vector<int>& vPiVarA,
    int skipPi,
    std::vector<int>& pattern
)
{
    int nPis = Abc_NtkPiNum(pNtk);
    pattern.assign(nPis, -1);

    for (int t = 0; t < nPis; ++t) {
        if (t == skipPi) {
            pattern[t] = -1; // print '-' for the variable under test
            continue;
        }

        int varA = vPiVarA[t];
        if (varA == -1) {
            pattern[t] = -1; // PI not in support of this output
            continue;
        }

        int val = sat_solver_var_value(pSat, varA); // 0 or 1
        pattern[t] = val ? 1 : 0;
    }
}
