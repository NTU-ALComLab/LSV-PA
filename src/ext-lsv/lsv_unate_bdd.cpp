#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/extrab/extraBdd.h"
#include "bdd/cudd/cudd.h"
#include "bdd/cudd/cuddInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include <algorithm>
#include <vector>
#include <string>
#include <iostream>
#include <cstdlib>

extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

// Forward declarations
static int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);
static void Lsv_CheckUnate(DdManager* dd, DdNode* func, int outputIdx, int inputIdx);
static void Lsv_CheckUnateSat(Abc_Ntk_t* pNtk, int outputIdx, int inputIdx);

// Module initialization for BDD unate checking
void initUnateBdd(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_bdd", Lsv_CommandUnateBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_unate_sat", Lsv_CommandUnateSat, 0);
}

void destroyUnateBdd(Abc_Frame_t* pAbc) {}

// Registrar for ABC framework
Abc_FrameInitializer_t frame_initializer_unate_bdd = {initUnateBdd, destroyUnateBdd};

struct UnateBddPackageRegistrationManager {
  UnateBddPackageRegistrationManager() { 
    Abc_FrameAddInitializer(&frame_initializer_unate_bdd); 
  }
} lsvUnateBddRegistrationManager;

//=============================================================================
// Command: lsv_unate_bdd <k> <i>
//=============================================================================

int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  
  // Check if network is loaded
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  // Check argument count
  if (argc != 3) {
    Abc_Print(-1, "Usage: lsv_unate_bdd <k> <i>\n");
    Abc_Print(-1, "  <k>: Primary output index (starting from 0)\n");
    Abc_Print(-1, "  <i>: Primary input index (starting from 0)\n");
    return 1;
  }

  // Parse arguments
  int outputIdx = std::atoi(argv[1]);
  int inputIdx = std::atoi(argv[2]);

  // Validate output index
  if (outputIdx < 0 || outputIdx >= Abc_NtkPoNum(pNtk)) {
    Abc_Print(-1, "Error: Output index %d out of range [0, %d)\n", 
              outputIdx, Abc_NtkPoNum(pNtk));
    return 1;
  }

  // Validate input index
  if (inputIdx < 0 || inputIdx >= Abc_NtkPiNum(pNtk)) {
    Abc_Print(-1, "Error: Input index %d out of range [0, %d)\n", 
              inputIdx, Abc_NtkPiNum(pNtk));
    return 1;
  }

  // Check if network is in BDD form (collapsed)
  if (!Abc_NtkIsBddLogic(pNtk)) {
    Abc_Print(-1, "Error: Network is not in BDD form. Run 'collapse' first.\n");
    return 1;
  }

  // Get BDD manager
  DdManager* dd = (DdManager*)pNtk->pManFunc;
  if (!dd) {
    Abc_Print(-1, "Error: BDD manager not found.\n");
    return 1;
  }

  // Get the output node
  Abc_Obj_t* pPo = Abc_NtkPo(pNtk, outputIdx);
  Abc_Obj_t* pNode = Abc_ObjFanin0(pPo);
  
  // Get the BDD function for this output
  DdNode* func = (DdNode*)pNode->pData;
  if (!func) {
    Abc_Print(-1, "Error: BDD function not found for output %d.\n", outputIdx);
    return 1;
  }

  // Complement if necessary
  if (Abc_ObjFaninC0(pPo)) {
    func = Cudd_Not(func);
  }

  // Perform unate check
  Lsv_CheckUnate(dd, func, outputIdx, inputIdx);

  return 0;
}

//=============================================================================
// Core Algorithm: Check if function is unate/binate
//=============================================================================

void Lsv_CheckUnate(DdManager* dd, DdNode* func, int outputIdx, int inputIdx) {
  // TODO: Implement the unate/binate checking algorithm
  // 
  // Algorithm outline:
  // 1. Compute positive cofactor: f_xi (f with xi = 1)
  // 2. Compute negative cofactor: f_~xi (f with xi = 0)
  // 3. Check relationships:
  //    - Positive unate: f_~xi ≤ f_xi  (f_~xi AND NOT f_xi = 0)
  //    - Negative unate: f_xi ≤ f_~xi  (f_xi AND NOT f_~xi = 0)
  //    - Independent: f_~xi = f_xi
  //    - Binate: otherwise
  // 4. If binate, find witness patterns
  DdNode* xi = Cudd_bddIthVar(dd, inputIdx);
  DdNode* not_xi = Cudd_Not(xi);

  DdNode* f_xi = Cudd_Cofactor(dd, func, xi);
  DdNode* f_not_xi = Cudd_Cofactor(dd, func, not_xi);
  Cudd_Ref(f_xi);
  Cudd_Ref(f_not_xi);

  if(f_xi == f_not_xi){
    std::cout << "independent\n";
    Cudd_RecursiveDeref(dd, f_xi);
    Cudd_RecursiveDeref(dd, f_not_xi);
    return;
  }

  DdNode* not_f_xi = Cudd_Not(f_xi);
  DdNode* bad_pos = Cudd_bddAnd(dd, f_not_xi, not_f_xi);
  Cudd_Ref(bad_pos);

  bool is_pos_unate = (bad_pos == Cudd_ReadLogicZero(dd));

  DdNode* not_f_not_xi = Cudd_Not(f_not_xi);
  DdNode* bad_neg = Cudd_bddAnd(dd, f_xi, not_f_not_xi);
  Cudd_Ref(bad_neg);

  bool is_neg_unate = (bad_neg == Cudd_ReadLogicZero(dd));

  if(is_pos_unate){
    std::cout << "positive unate\n";
  }
  else if(is_neg_unate){
    std::cout << "negative unate\n";
  }
  else{
    std::cout << "binate\n";

    // Find witness patterns using Cudd_bddPickOneCube
    int numVars = Cudd_ReadSize(dd);
    char* pattern1 = new char[numVars];
    char* pattern2 = new char[numVars];

    // Initialize patterns
    for(int i = 0; i < numVars; i++){
      pattern1[i] = 2; // 2 means don't care
      pattern2[i] = 2;
    }

    // Get pattern 1: where f_not_xi AND NOT f_xi is true
    if(bad_pos != Cudd_ReadLogicZero(dd)){
      Cudd_bddPickOneCube(dd, bad_pos, pattern1);
    }

    // Get pattern 2: where f_xi AND NOT f_not_xi is true
    if(bad_neg != Cudd_ReadLogicZero(dd)){
      Cudd_bddPickOneCube(dd, bad_neg, pattern2);
    }

    // Print pattern 1
    for(int i = 0; i < numVars; i++){
      if(i == inputIdx){
        std::cout << "-";
      } else if(pattern1[i] == 0){
        std::cout << "0";
      } else if(pattern1[i] == 1){
        std::cout << "1";
      } else {
        std::cout << "0"; // Default to 0 for don't care
      }
    }
    std::cout << "\n";

    // Print pattern 2
    for(int i = 0; i < numVars; i++){
      if(i == inputIdx){
        std::cout << "-";
      } else if(pattern2[i] == 0){
        std::cout << "0";
      } else if(pattern2[i] == 1){
        std::cout << "1";
      } else {
        std::cout << "1"; // Default to 1 for don't care
      }
    }
    std::cout << "\n";

    delete[] pattern1;
    delete[] pattern2;
  }

  // Clean up
  Cudd_RecursiveDeref(dd, f_xi);
  Cudd_RecursiveDeref(dd, f_not_xi);
  Cudd_RecursiveDeref(dd, bad_pos);
  Cudd_RecursiveDeref(dd, bad_neg);
}

//=============================================================================
// Command: lsv_unate_sat <k> <i>
//=============================================================================

int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  
  // Check if network is loaded
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  // Check argument count
  if (argc != 3) {
    Abc_Print(-1, "Usage: lsv_unate_sat <k> <i>\n");
    Abc_Print(-1, "  <k>: Primary output index (starting from 0)\n");
    Abc_Print(-1, "  <i>: Primary input index (starting from 0)\n");
    return 1;
  }

  // Parse arguments
  int outputIdx = std::atoi(argv[1]);
  int inputIdx = std::atoi(argv[2]);

  // Validate output index
  if (outputIdx < 0 || outputIdx >= Abc_NtkPoNum(pNtk)) {
    Abc_Print(-1, "Error: Output index %d out of range [0, %d)\n", 
              outputIdx, Abc_NtkPoNum(pNtk));
    return 1;
  }

  // Validate input index
  if (inputIdx < 0 || inputIdx >= Abc_NtkPiNum(pNtk)) {
    Abc_Print(-1, "Error: Input index %d out of range [0, %d)\n", 
              inputIdx, Abc_NtkPiNum(pNtk));
    return 1;
  }

  // Check if network is strashed (AIG form)
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "Error: Network is not in AIG form. Run 'strash' first.\n");
    return 1;
  }

  // Perform SAT-based unate check
  Lsv_CheckUnateSat(pNtk, outputIdx, inputIdx);

  return 0;
}

//=============================================================================
// Core Algorithm: SAT-based unate checking
//=============================================================================

void Lsv_CheckUnateSat(Abc_Ntk_t* pNtk, int outputIdx, int inputIdx) {
  // Step 1: Extract the cone of output yk
  Abc_Obj_t* pPo = Abc_NtkPo(pNtk, outputIdx);
  Abc_Ntk_t* pCone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pPo), 
                                        Abc_ObjName(pPo), 1);
  
  if (!pCone) {
    Abc_Print(-1, "Error: Failed to create cone for output %d.\n", outputIdx);
    return;
  }

  // Step 2: Convert to AIG
  Aig_Man_t* pAig = Abc_NtkToDar(pCone, 0, 0);
  if (!pAig) {
    Abc_Print(-1, "Error: Failed to convert network to AIG.\n");
    Abc_NtkDelete(pCone);
    return;
  }

  // Step 3: Initialize SAT solver
  sat_solver* pSat = sat_solver_new();

  // Step 4 & 5: Derive CNF for first copy (CA) and add to solver
  Cnf_Dat_t* pCnfA = Cnf_Derive(pAig, 1);
  Cnf_DataWriteIntoSolverInt(pSat, pCnfA, 1, 0);

  // Step 6: Create second CNF (CB) with lifted variables
  Cnf_Dat_t* pCnfB = Cnf_DataDup(pCnfA);
  Cnf_DataLift(pCnfB, pCnfA->nVars);
  Cnf_DataWriteIntoSolverInt(pSat, pCnfB, 1, 0);

  // Step 7: Set vA(t) = vB(t) for all inputs except xi
  // Find the input object for xi in the cone
  Abc_Obj_t* pPi;
  Abc_Obj_t* pPiTarget = Abc_NtkPi(pNtk, inputIdx);
  int i;
  
  Abc_NtkForEachPi(pCone, pPi, i) {
    // Skip the target input xi
    if (Abc_ObjId(pPi) == Abc_ObjId(pPiTarget)) {
      continue;
    }
    
    // Get corresponding AIG object
    Aig_Obj_t* pAigObj = Aig_ManCi(pAig, i);
    int varA = pCnfA->pVarNums[pAigObj->Id];
    int varB = pCnfB->pVarNums[pAigObj->Id];
    
    if (varA >= 0 && varB >= 0) {
      // Add clauses: (varA -> varB) AND (varB -> varA)
      // Which is: (!varA OR varB) AND (varA OR !varB)
      int lits[2];
      
      lits[0] = toLitCond(varA, 1); // !varA
      lits[1] = toLitCond(varB, 0); // varB
      sat_solver_addclause(pSat, lits, lits + 2);
      
      lits[0] = toLitCond(varA, 0); // varA
      lits[1] = toLitCond(varB, 1); // !varB
      sat_solver_addclause(pSat, lits, lits + 2);
    }
  }

  // Get output variables
  Aig_Obj_t* pAigPo = Aig_ManCo(pAig, 0);
  int outVarA = pCnfA->pVarNums[Aig_ObjFanin0(pAigPo)->Id];
  int outVarB = pCnfB->pVarNums[Aig_ObjFanin0(pAigPo)->Id];

  // Adjust for complemented edges
  int outLitA = toLitCond(outVarA, Aig_ObjFaninC0(pAigPo));
  int outLitB = toLitCond(outVarB, Aig_ObjFaninC0(pAigPo));

  // Step 8: Check different conditions
  int assumps[2];
  int statusIndep1, statusIndep2, statusPos, statusNeg;
  bool isIndependent = false;
  bool isPosUnate = false;
  bool isNegUnate = false;
  
  // Check independence: fA XOR fB should be UNSAT
  assumps[0] = outLitA;
  assumps[1] = lit_neg(outLitB);
  statusIndep1 = sat_solver_solve(pSat, assumps, assumps + 2, 0, 0, 0, 0);
  
  assumps[0] = lit_neg(outLitA);
  assumps[1] = outLitB;
  statusIndep2 = sat_solver_solve(pSat, assumps, assumps + 2, 0, 0, 0, 0);
  
  if (statusIndep1 == l_False && statusIndep2 == l_False) {
    isIndependent = true;
  }
  else {
    // Check positive unate: fB AND !fA should be UNSAT
    assumps[0] = outLitB;
    assumps[1] = lit_neg(outLitA);
    statusPos = sat_solver_solve(pSat, assumps, assumps + 2, 0, 0, 0, 0);
    
    if (statusPos == l_False) {
      isPosUnate = true;
    }
    else {
      // Check negative unate: fA AND !fB should be UNSAT
      assumps[0] = outLitA;
      assumps[1] = lit_neg(outLitB);
      statusNeg = sat_solver_solve(pSat, assumps, assumps + 2, 0, 0, 0, 0);
      
      if (statusNeg == l_False) {
        isNegUnate = true;
      }
    }
  }

  // Output results
  if (isIndependent) {
    std::cout << "independent\n";
  }
  else if (isPosUnate) {
    std::cout << "positive unate\n";
  }
  else if (isNegUnate) {
    std::cout << "negative unate\n";
  }
  else {
    // Binate case
    std::cout << "binate\n";
    
    // Step 9: Extract witness patterns from SAT model
    // Pattern 1: fB=1 and fA=0 (shows positive dependency on xi)
    assumps[0] = outLitB;
    assumps[1] = lit_neg(outLitA);
    int status1 = sat_solver_solve(pSat, assumps, assumps + 2, 0, 0, 0, 0);
    
    if (status1 == l_True) {
      // Extract pattern 1
      Abc_NtkForEachPi(pCone, pPi, i) {
        Aig_Obj_t* pAigObj = Aig_ManCi(pAig, i);
        int varA = pCnfA->pVarNums[pAigObj->Id];
        
        if (Abc_ObjId(pPi) == Abc_ObjId(pPiTarget)) {
          // This is xi, print '-'
          std::cout << "-";
        } else if (varA >= 0) {
          // Get value from SAT model
          int val = sat_solver_var_value(pSat, varA);
          std::cout << val;
        } else {
          std::cout << "0";
        }
      }
      std::cout << "\n";
    }
    
    // Pattern 2: fA=1 and fB=0 (shows negative dependency on xi)
    assumps[0] = outLitA;
    assumps[1] = lit_neg(outLitB);
    int status2 = sat_solver_solve(pSat, assumps, assumps + 2, 0, 0, 0, 0);
    
    if (status2 == l_True) {
      // Extract pattern 2
      Abc_NtkForEachPi(pCone, pPi, i) {
        Aig_Obj_t* pAigObj = Aig_ManCi(pAig, i);
        int varA = pCnfA->pVarNums[pAigObj->Id];
        
        if (Abc_ObjId(pPi) == Abc_ObjId(pPiTarget)) {
          // This is xi, print '-'
          std::cout << "-";
        } else if (varA >= 0) {
          // Get value from SAT model
          int val = sat_solver_var_value(pSat, varA);
          std::cout << val;
        } else {
          std::cout << "0";
        }
      }
      std::cout << "\n";
    }
  }

  // Clean up
  sat_solver_delete(pSat);
  Cnf_DataFree(pCnfA);
  Cnf_DataFree(pCnfB);
  Aig_ManStop(pAig);
  Abc_NtkDelete(pCone);
}
