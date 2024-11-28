#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include <vector>
#include <set>
#include <map>
#include <iostream>

extern "C" {
    Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}

// void PrintConeStructure(Abc_Ntk_t* pCone) {
//     printf("\nCone Network Structure:\n");
//     printf("------------------------\n");
    
//     printf("Network Statistics:\n");
//     printf("  Nodes: %d\n", Abc_NtkNodeNum(pCone));
//     printf("  Primary Inputs: %d\n", Abc_NtkPiNum(pCone));
//     printf("  Primary Outputs: %d\n", Abc_NtkPoNum(pCone));
    
//     Abc_Obj_t* pObj;
//     int i;
    
//     printf("\nPrimary Inputs:\n");
//     Abc_NtkForEachPi(pCone, pObj, i) {
//         printf("  PI %d: Name = %s, ID = %d\n", 
//                i, Abc_ObjName(pObj), Abc_ObjId(pObj));
//     }
    
//     printf("\nNodes:\n");
//     Abc_NtkForEachNode(pCone, pObj, i) {
//         printf("  Node %d: Name = %s, ID = %d\n", 
//                i, Abc_ObjName(pObj), Abc_ObjId(pObj));
//         printf("    Fanins: ");
//         Abc_Obj_t* pFanin;
//         int j;
//         Abc_ObjForEachFanin(pObj, pFanin, j) {
//             printf("(%d%s) ", Abc_ObjId(pFanin), 
//                    Abc_ObjFaninC(pObj, j) ? "'" : "");
//         }
//         printf("\n");
//     }
    
//     printf("\nPrimary Outputs:\n");
//     Abc_NtkForEachPo(pCone, pObj, i) {
//         printf("  PO %d: Name = %s, ID = %d\n", 
//                i, Abc_ObjName(pObj), Abc_ObjId(pObj));
//         printf("    Driver: %d%s\n", 
//                Abc_ObjId(Abc_ObjFanin0(pObj)),
//                Abc_ObjFaninC0(pObj) ? "'" : "");
//     }
// }

// void PrintAigStructure(Aig_Man_t* pAig) {
//     printf("\nAIG Structure:\n");
//     printf("---------------\n");
//     printf("Statistics:\n");
//     printf("  Total nodes: %d\n", Aig_ManNodeNum(pAig));
//     printf("  Total objects: %d\n", Aig_ManObjNum(pAig));
//     printf("  Constant nodes: %d\n", Aig_ManConst1(pAig) != NULL);
    
//     Aig_Obj_t* pObj;
//     int i;
    
//     printf("\nObjects by type:\n");
//     Aig_ManForEachObj(pAig, pObj, i) {
//         if (Aig_ObjIsConst1(pObj))
//             printf("  Const1 node: ID = %d\n", Aig_ObjId(pObj));
//         else if (Aig_ObjIsCi(pObj))
//             printf("  CI: ID = %d\n", Aig_ObjId(pObj));
//         else if (Aig_ObjIsCo(pObj))
//             printf("  CO: ID = %d, Driver = %d%s\n", 
//                    Aig_ObjId(pObj), Aig_ObjFaninId0(pObj),
//                    Aig_ObjFaninC0(pObj) ? "'" : "");
//         else if (Aig_ObjIsNode(pObj)) {
//             printf("  AND: ID = %d\n", Aig_ObjId(pObj));
//             printf("    Fanin0: %d%s\n", 
//                    Aig_ObjFaninId0(pObj),
//                    Aig_ObjFaninC0(pObj) ? "'" : "");
//             printf("    Fanin1: %d%s\n", 
//                    Aig_ObjFaninId1(pObj),
//                    Aig_ObjFaninC1(pObj) ? "'" : "");
//         }
//     }
// }

// void PrintCnfClauses(sat_solver* pSat, const std::map<int, int>& nodeToVar, const std::vector<std::vector<lit>>& allClauses) {
//     printf("\nCNF Structure:\n");
//     printf("--------------\n");
//     printf("Total Variables: %d\n", sat_solver_nvars(pSat));
    
//     printf("\nVariable Mapping (AIG Node -> CNF Variable):\n");
//     for (const auto& pair : nodeToVar) {
//         printf("  AIG Node %d -> CNF Var %d\n", pair.first, pair.second);
//     }
    
//     printf("\nClauses:\n");
//     for (size_t i = 0; i < allClauses.size(); i++) {
//         printf("Clause %zu: ", i);
//         for (lit literal : allClauses[i]) {
//             int var = lit_var(literal);
//             int sign = lit_sign(literal);
            
//             // Find corresponding AIG node if it exists
//             int aigNode = -1;
//             for (const auto& pair : nodeToVar) {
//                 if (pair.second == var) {
//                     aigNode = pair.first;
//                     break;
//                 }
//             }
            
//             if (aigNode != -1) {
//                 printf("%s%d(AIG:%d) ", sign ? "¬" : "", var, aigNode);
//             } else {
//                 printf("%s%d ", sign ? "¬" : "", var);
//             }
//         }
//         printf("\n");
//     }
// }

bool isPatternPossible(Abc_Obj_t* pNode, int val0, int val1) {
    //printf("\nChecking pattern (%d,%d) for node %d\n", val0, val1, Abc_ObjId(pNode));
    
    Abc_Ntk_t* pNtk = Abc_ObjNtk(pNode);
    Abc_Obj_t* pFanin0 = Abc_ObjFanin0(pNode);
    Abc_Obj_t* pFanin1 = Abc_ObjFanin1(pNode);
    
    Vec_Ptr_t* vNodes = Vec_PtrAlloc(2);
    Vec_PtrPush(vNodes, pFanin0);
    Vec_PtrPush(vNodes, pFanin1);
    
    Abc_Ntk_t* pCone = Abc_NtkCreateConeArray(pNtk, vNodes, 1);
    //PrintConeStructure(pCone);
    Vec_PtrFree(vNodes);
    if (!pCone) return true;
    
    Aig_Man_t* pAig = Abc_NtkToDar(pCone, 0, 0);
    //PrintAigStructure(pAig);
    Abc_NtkDelete(pCone);
    if (!pAig) return true;
    
    sat_solver* pSat = sat_solver_new();
    int nVars = 2 * Aig_ManObjNumMax(pAig);
    sat_solver_setnvars(pSat, nVars);
    
    std::map<int, int> nodeToVar;
    int varCounter = 1;
    
    // Map combinational inputs to variables
    Aig_Obj_t* pObj;
    int i;
    Aig_ManForEachCi(pAig, pObj, i) {
        nodeToVar[Aig_ObjId(pObj)] = varCounter++;
    }
    
    std::vector<std::vector<lit>> allClauses;
    
    // When creating clauses for AND gates, store them in allClauses
    Aig_ManForEachNode(pAig, pObj, i) {
        int outVar = varCounter++;
        nodeToVar[Aig_ObjId(pObj)] = outVar;
        
        int in0Var = nodeToVar[Aig_ObjFaninId0(pObj)];
        int in1Var = nodeToVar[Aig_ObjFaninId1(pObj)];
        bool isIn0Compl = Aig_ObjFaninC0(pObj);
        bool isIn1Compl = Aig_ObjFaninC1(pObj);
        
        // Create clauses for AND gate
        lit Lits[3];
        
        // First clause: (!out + in0)
        std::vector<lit> clause1 = {toLitCond(outVar, 1), toLitCond(in0Var, isIn0Compl)};
        allClauses.push_back(clause1);
        Lits[0] = clause1[0];
        Lits[1] = clause1[1];
        if (!sat_solver_addclause(pSat, Lits, Lits + 2)) {
            sat_solver_delete(pSat);
            Aig_ManStop(pAig);
            return false;
        }
        
        // Second clause: (!out + in1)
        std::vector<lit> clause2 = {toLitCond(outVar, 1), toLitCond(in1Var, isIn1Compl)};
        allClauses.push_back(clause2);
        Lits[0] = clause2[0];
        Lits[1] = clause2[1];
        if (!sat_solver_addclause(pSat, Lits, Lits + 2)) {
            sat_solver_delete(pSat);
            Aig_ManStop(pAig);
            return false;
        }
        
        // Third clause: (out + !in0 + !in1)
        std::vector<lit> clause3 = {toLitCond(outVar, 0), 
                                   toLitCond(in0Var, !isIn0Compl),
                                   toLitCond(in1Var, !isIn1Compl)};
        allClauses.push_back(clause3);
        Lits[0] = clause3[0];
        Lits[1] = clause3[1];
        Lits[2] = clause3[2];
        if (!sat_solver_addclause(pSat, Lits, Lits + 3)) {
            sat_solver_delete(pSat);
            Aig_ManStop(pAig);
            return false;
        }
    }
    
    // Add output constraints
    int fanin0Compl = Abc_ObjFaninC0(pNode);  // Get complemented status of first fanin
    int fanin1Compl = Abc_ObjFaninC1(pNode);  // Get complemented status of second fanin

    Aig_ManForEachCo(pAig, pObj, i) {
        int driverId = Aig_ObjFaninId0(pObj);
        int isCompl = Aig_ObjFaninC0(pObj);
        int outVar = nodeToVar[driverId];

        //std::cout << "DriverID: " << driverId << ", isCompl: " << isCompl << ", outVar: " << outVar << ", fanin0Compl: " << fanin0Compl << ", fanin1Compl: " << fanin1Compl << std::endl;
        
        lit Lits[1];
        if (i == 0) {
            // For first fanin: consider both the original fanin complement and AIG complement
            Lits[0] = toLitCond(outVar, !(val0 ^ fanin0Compl ^ isCompl));
        } else {
            // For second fanin
            Lits[0] = toLitCond(outVar, !(val1 ^ fanin1Compl ^ isCompl));
        }
        
        std::vector<lit> clause = {Lits[0]};
        allClauses.push_back(clause);
        
        if (!sat_solver_addclause(pSat, Lits, Lits + 1)) {
            sat_solver_delete(pSat);
            Aig_ManStop(pAig);
            return false;
        }
    }
    
    //PrintCnfClauses(pSat, nodeToVar, allClauses);
    
    int status = sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);
    //printf("SAT solver status: %s\n", status == l_True ? "SAT" : "UNSAT");
    
    sat_solver_delete(pSat);
    Aig_ManStop(pAig);
    
    return status == l_True;
}

struct OdcResult {
    std::vector<std::pair<int, int>> odcPatterns;
    bool success;
};

void PrintMiterStructure(Abc_Ntk_t* pMiter) {
    printf("\nMiter Network Structure:\n");
    printf("------------------------\n");
    printf("Network Statistics:\n");
    printf("  Nodes: %d\n", Abc_NtkNodeNum(pMiter));
    printf("  Primary Inputs: %d\n", Abc_NtkPiNum(pMiter));
    printf("  Primary Outputs: %d\n", Abc_NtkPoNum(pMiter));
    
    Abc_Obj_t* pObj;
    int i;
    
    printf("\nPrimary Inputs:\n");
    Abc_NtkForEachPi(pMiter, pObj, i) {
        printf("  PI %d: Name = %s, ID = %d\n", 
               i, Abc_ObjName(pObj), Abc_ObjId(pObj));
    }
    
    printf("\nNodes:\n");
    Abc_NtkForEachNode(pMiter, pObj, i) {
        printf("  Node %d: Name = %s, ID = %d\n", 
               i, Abc_ObjName(pObj), Abc_ObjId(pObj));
        printf("    Fanins: ");
        Abc_Obj_t* pFanin;
        int j;
        Abc_ObjForEachFanin(pObj, pFanin, j) {
            printf("(%d%s) ", Abc_ObjId(pFanin), 
                   Abc_ObjFaninC(pObj, j) ? "'" : "");
        }
        printf("\n");
    }
}

void PrintAigStructure(Aig_Man_t* pAig) {
    printf("\nAIG Structure:\n");
    printf("---------------\n");
    printf("Statistics:\n");
    printf("  Total nodes: %d\n", Aig_ManNodeNum(pAig));
    printf("  Total objects: %d\n", Aig_ManObjNum(pAig));
    printf("  Constant nodes: %d\n", Aig_ManConst1(pAig) != NULL);
    
    Aig_Obj_t* pObj;
    int i;
    
    printf("\nObjects by type:\n");
    Aig_ManForEachObj(pAig, pObj, i) {
        if (Aig_ObjIsConst1(pObj))
            printf("  Const1 node: ID = %d\n", Aig_ObjId(pObj));
        else if (Aig_ObjIsCi(pObj))
            printf("  CI: ID = %d\n", Aig_ObjId(pObj));
        else if (Aig_ObjIsCo(pObj))
            printf("  CO: ID = %d, Driver = %d%s\n", 
                   Aig_ObjId(pObj), Aig_ObjFaninId0(pObj),
                   Aig_ObjFaninC0(pObj) ? "'" : "");
        else if (Aig_ObjIsNode(pObj)) {
            printf("  AND: ID = %d\n", Aig_ObjId(pObj));
            printf("    Fanin0: %d%s\n", 
                   Aig_ObjFaninId0(pObj),
                   Aig_ObjFaninC0(pObj) ? "'" : "");
            printf("    Fanin1: %d%s\n", 
                   Aig_ObjFaninId1(pObj),
                   Aig_ObjFaninC1(pObj) ? "'" : "");
        }
    }
}

void PrintCnfInfo(Cnf_Dat_t* pCnf) {
    printf("\nCNF Structure:\n");
    printf("--------------\n");
    printf("Number of variables: %d\n", pCnf->nVars);
    printf("Number of clauses: %d\n", pCnf->nClauses);
    printf("\nVariable mapping (AIG Node -> CNF Variable):\n");
    for (int i = 0; i < pCnf->nVars; i++) {
        if (pCnf->pVarNums[i] != -1) {
            printf("  AIG Node %d -> CNF Var %d\n", i, pCnf->pVarNums[i]);
        }
    }
    
    printf("\nFirst few clauses:\n");
    for (int i = 0; i < std::min(5, pCnf->nClauses); i++) {
        printf("Clause %d: ", i);
        int* pClause = pCnf->pClauses[i];
        int j = 0;
        while (pClause[j]) {
            printf("%s%d ", (pClause[j] & 1) ? "¬" : "", pClause[j]/2);
            j++;
        }
        printf("\n");
    }
}

void PrintConeStructure(Abc_Ntk_t* pCone, const char* title) {
    printf("\n%s Network Structure:\n", title);
    printf("------------------------\n");
    printf("Network Statistics:\n");
    printf("  Nodes: %d\n", Abc_NtkNodeNum(pCone));
    printf("  Primary Inputs: %d\n", Abc_NtkPiNum(pCone));
    printf("  Primary Outputs: %d\n", Abc_NtkPoNum(pCone));
    
    Abc_Obj_t* pObj;
    int i;
    
    printf("\nPrimary Inputs:\n");
    Abc_NtkForEachPi(pCone, pObj, i) {
        printf("  PI %d: Name = %s, ID = %d\n", 
               i, Abc_ObjName(pObj), Abc_ObjId(pObj));
    }
    
    printf("\nNodes:\n");
    Abc_NtkForEachNode(pCone, pObj, i) {
        printf("  Node %d: Name = %s, ID = %d\n", 
               i, Abc_ObjName(pObj), Abc_ObjId(pObj));
        printf("    Fanins: ");
        Abc_Obj_t* pFanin;
        int j;
        Abc_ObjForEachFanin(pObj, pFanin, j) {
            printf("(%d%s) ", Abc_ObjId(pFanin), 
                   Abc_ObjFaninC(pObj, j) ? "'" : "");
        }
        printf("\n");
    }
    
    printf("\nPrimary Outputs:\n");
    Abc_NtkForEachPo(pCone, pObj, i) {
        printf("  PO %d: Name = %s, ID = %d\n", 
               i, Abc_ObjName(pObj), Abc_ObjId(pObj));
        Abc_Obj_t* pDriver = Abc_ObjFanin0(pObj);
        printf("    Driver: %d%s\n", 
               Abc_ObjId(pDriver),
               Abc_ObjFaninC0(pObj) ? "'" : "");
    }
}

OdcResult calculateOdc(Abc_Ntk_t* pNtk, Abc_Obj_t* pNode) {
    OdcResult result;
    result.success = false;
    
    printf("\n=== Starting ODC Calculation for Node %d ===\n", Abc_ObjId(pNode));
    printf("Network Statistics:\n");
    printf("Total nodes: %d\n", Abc_NtkNodeNum(pNtk));
    printf("Primary inputs: %d\n", Abc_NtkPiNum(pNtk));
    printf("Primary outputs: %d\n", Abc_NtkPoNum(pNtk));
    printf("\nTarget node %d information:\n", Abc_ObjId(pNode));
    printf("Fanin0: %d, Fanin1: %d\n", Abc_ObjId(Abc_ObjFanin0(pNode)), Abc_ObjId(Abc_ObjFanin1(pNode)));
    printf("Fanin0 complement: %d, Fanin1 complement: %d\n", Abc_ObjFaninC0(pNode), Abc_ObjFaninC1(pNode));
    
    printf("\nFanouts of node %d:\n", Abc_ObjId(pNode));
    Abc_Obj_t* pFanout;
    int i;
    Abc_ObjForEachFanout(pNode, pFanout, i) {
        printf("Fanout %d: ID = %d, Type = %d\n", i, Abc_ObjId(pFanout), Abc_ObjType(pFanout));
    }
    
    // Create first network copy
    printf("\nCreating first network copy\n");
    Abc_Ntk_t* pNtk1 = Abc_NtkDup(pNtk);
    if (!pNtk1) {
        printf("ERROR: Failed to create first network copy\n");
        return result;
    }
    
    // Create second network copy
    printf("\nCreating second network copy\n");
    Abc_Ntk_t* pNtk2 = Abc_NtkDup(pNtk);
    if (!pNtk2) {
        printf("ERROR: Failed to create second network copy\n");
        Abc_NtkDelete(pNtk1);
        return result;
    }
    
    // Find corresponding node in second network
    Abc_Obj_t* pNode2 = Abc_NtkObj(pNtk2, Abc_ObjId(pNode));
    printf("\nIdentified corresponding node in second network: %d\n", Abc_ObjId(pNode2));
    
    // Complement the node in second network
    printf("\nComplementing node in second network\n");
    Abc_ObjForEachFanout(pNode2, pFanout, i) {
        int faninNum = Abc_ObjFanoutFaninNum(pFanout, pNode2);
        printf("Complementing edge to fanout %d (fanin number %d)\n", Abc_ObjId(pFanout), faninNum);
        Abc_ObjXorFaninC(pFanout, faninNum);
    }
    
    // Create miter network
    printf("\nCreating miter network\n");
    Abc_Ntk_t* pMiter = Abc_NtkMiter(pNtk1, pNtk2, 1, 0, 0, 0);
    if (!pMiter) {
        printf("ERROR: Failed to create miter network\n");
        Abc_NtkDelete(pNtk2);
        Abc_NtkDelete(pNtk1);
        return result;
    }
    printf("Miter network created successfully\n");
    printf("Miter network statistics:\n");
    printf("Nodes: %d\n", Abc_NtkNodeNum(pMiter));
    printf("PIs: %d\n", Abc_NtkPiNum(pMiter));
    printf("POs: %d\n", Abc_NtkPoNum(pMiter));
    PrintMiterStructure(pMiter);
    
    // Convert to AIG
    printf("\nConverting miter to AIG\n");
    Aig_Man_t* pAig = Abc_NtkToDar(pMiter, 0, 0);
    if (!pAig) {
        printf("ERROR: Failed to convert to AIG\n");
        Abc_NtkDelete(pMiter);
        Abc_NtkDelete(pNtk2);
        Abc_NtkDelete(pNtk1);
        return result;
    }
    
    // Print AIG structure
    printf("AIG created with:\n");
    printf("Nodes: %d\n", Aig_ManNodeNum(pAig));
    printf("Total objects: %d\n", Aig_ManObjNum(pAig));
    PrintAigStructure(pAig);
    
    // Convert AIG to CNF
    printf("\nConverting AIG to CNF\n");
    Cnf_Dat_t* pCnf = Cnf_Derive(pAig, 0);
    if (!pCnf) {
        printf("ERROR: Failed to create CNF\n");
        Aig_ManStop(pAig);
        Abc_NtkDelete(pMiter);
        Abc_NtkDelete(pNtk2);
        Abc_NtkDelete(pNtk1);
        return result;
    }
    
    printf("CNF created with:\n");
    printf("Variables: %d\n", pCnf->nVars);
    printf("Clauses: %d\n", pCnf->nClauses);
    PrintCnfInfo(pCnf);
    
    // Print variable mapping
    printf("\nVariable mapping (AIG Node -> CNF Variable):\n");
    printf("Node fanin0 (ID %d) -> CNF var %d\n", 
           Abc_ObjId(Abc_ObjFanin0(pNode)),
           pCnf->pVarNums[Abc_ObjId(Abc_ObjFanin0(pNode))]);
    printf("Node fanin1 (ID %d) -> CNF var %d\n", 
           Abc_ObjId(Abc_ObjFanin1(pNode)),
           pCnf->pVarNums[Abc_ObjId(Abc_ObjFanin1(pNode))]);
    
    // Initialize SAT solver
    printf("\nInitializing SAT solver\n");
    sat_solver* pSat = sat_solver_new();
    sat_solver_setnvars(pSat, pCnf->nVars);
    
    // Add CNF clauses to SAT solver
    printf("Adding CNF clauses to SAT solver\n");
    for (int i = 0; i < pCnf->nClauses; i++) {
        int* pClause = pCnf->pClauses[i];
        int j = 0;
        while (pClause[j]) j++;
        printf("Adding clause %d of length %d: ", i, j);
        for (int k = 0; k < j; k++) {
            printf("%d ", pClause[k]);
        }
        printf("\n");
        
        if (!sat_solver_addclause(pSat, pClause, pClause + j)) {
            printf("ERROR: Failed to add clause %d\n", i);
            Cnf_DataFree(pCnf);
            sat_solver_delete(pSat);
            Aig_ManStop(pAig);
            Abc_NtkDelete(pMiter);
            Abc_NtkDelete(pNtk2);
            Abc_NtkDelete(pNtk1);
            return result;
        }
    }
    
    // Add miter output constraint
    printf("\nAdding miter output constraint\n");
    Aig_Obj_t* pMiterOut = Aig_ManCo(pAig, 0);
    printf("Miter output node ID: %d\n", Aig_ObjId(pMiterOut));
    printf("Corresponding CNF variable: %d\n", pCnf->pVarNums[Aig_ObjId(pMiterOut)]);
    
    lit Lits[1];
    Lits[0] = toLitCond(pCnf->pVarNums[Aig_ObjId(pMiterOut)], 0);
    if (!sat_solver_addclause(pSat, Lits, Lits + 1)) {
        printf("ERROR: Failed to add miter output constraint\n");
    }
    
    // Find care set patterns
    printf("\nFinding care set patterns\n");
    std::set<std::pair<int, int>> careSet;
    
    // Track node IDs for debugging
    int fanin0Id = Abc_ObjId(Abc_ObjFanin0(pNode));
    int fanin1Id = Abc_ObjId(Abc_ObjFanin1(pNode));
    printf("Using fanin IDs: %d, %d\n", fanin0Id, fanin1Id);
    printf("Corresponding CNF variables: %d, %d\n", 
           pCnf->pVarNums[fanin0Id],
           pCnf->pVarNums[fanin1Id]);
    
    // Verify variable indices are valid
    if (pCnf->pVarNums[fanin0Id] < 0 || pCnf->pVarNums[fanin0Id] >= pCnf->nVars ||
        pCnf->pVarNums[fanin1Id] < 0 || pCnf->pVarNums[fanin1Id] >= pCnf->nVars) {
        printf("ERROR: Invalid CNF variable indices\n");
        Cnf_DataFree(pCnf);
        sat_solver_delete(pSat);
        Aig_ManStop(pAig);
        Abc_NtkDelete(pMiter);
        Abc_NtkDelete(pNtk2);
        Abc_NtkDelete(pNtk1);
        return result;
    }
    
    while (1) {
        int status = sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);
        if (status != l_True) {
            printf("No more satisfying assignments found\n");
            break;
        }
        
        int val0 = sat_solver_var_value(pSat, pCnf->pVarNums[fanin0Id]);
        int val1 = sat_solver_var_value(pSat, pCnf->pVarNums[fanin1Id]);
        printf("Found care pattern: (%d, %d)\n", val0, val1);
        
        careSet.insert({val0, val1});
        
        lit blockLits[2];
        blockLits[0] = toLitCond(pCnf->pVarNums[fanin0Id], !val0);
        blockLits[1] = toLitCond(pCnf->pVarNums[fanin1Id], !val1);
        if (!sat_solver_addclause(pSat, blockLits, blockLits + 2)) {
            printf("Failed to add blocking clause\n");
            break;
        }
    }
    
    // Compute ODC patterns
    printf("\nComputing ODC patterns\n");
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            printf("Testing pattern (%d, %d)\n", i, j);
            if (careSet.find({i, j}) == careSet.end()) {
                if (isPatternPossible(pNode, i, j)) {
                    printf("Found ODC pattern: %d%d\n", i, j);
                    result.odcPatterns.push_back({i, j});
                }
            }
        }
    }
    
    // Cleanup
    printf("\nCleaning up resources\n");
    Cnf_DataFree(pCnf);
    sat_solver_delete(pSat);
    Aig_ManStop(pAig);
    Abc_NtkDelete(pMiter);
    Abc_NtkDelete(pNtk2);
    Abc_NtkDelete(pNtk1);
    
    result.success = true;
    return result;
}

int Lsv_CommandSdc(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
                Abc_Print(-2, "usage: lsv_sdc <node>\n");
                Abc_Print(-2, "\t        compute satisfiability don't cares for the specified node\n");
                Abc_Print(-2, "\t-h    : print the command usage\n");
                return 1;
        }
    }
    
    if (argc != 2) {
        Abc_Print(-1, "Missing node index.\n");
        Abc_Print(-2, "usage: lsv_sdc <node>\n");
        return 1;
    }
    
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    
    int nodeIndex = atoi(argv[1]);
    Abc_Obj_t* pNode = Abc_NtkObj(pNtk, nodeIndex);
    
    if (!pNode || !Abc_ObjIsNode(pNode)) {
        Abc_Print(-1, "Invalid node index.\n");
        return 1;
    }
    
    std::vector<std::pair<int, int>> sdcPatterns;
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            if (!isPatternPossible(pNode, i, j)) {
                sdcPatterns.push_back({i, j});
            }
        }
    }
    
    if (sdcPatterns.empty()) {
        Abc_Print(1, "no sdc\n");
    } else {
        for (const auto& pattern : sdcPatterns) {
            Abc_Print(1, "%d%d\n", pattern.first, pattern.second);
        }
    }
    
    return 0;
}

int Lsv_CommandOdc(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
                Abc_Print(-2, "usage: lsv_odc <node>\n");
                Abc_Print(-2, "\t        compute observability don't cares for the specified node\n");
                Abc_Print(-2, "\t-h    : print the command usage\n");
                return 1;
        }
    }
    
    if (argc != 2) {
        Abc_Print(-1, "Missing node index.\n");
        Abc_Print(-2, "usage: lsv_odc <node>\n");
        return 1;
    }
    
    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    
    int nodeIndex = atoi(argv[1]);
    Abc_Obj_t* pNode = Abc_NtkObj(pNtk, nodeIndex);
    
    if (!pNode || !Abc_ObjIsNode(pNode)) {
        Abc_Print(-1, "Invalid node index.\n");
        return 1;
    }
    
    // Calculate ODCs
    OdcResult result = calculateOdc(pNtk, pNode);
    
    if (!result.success) {
        Abc_Print(-1, "Failed to compute ODCs.\n");
        return 1;
    }
    
    // Output results
    if (result.odcPatterns.empty()) {
        Abc_Print(1, "no odc\n");
    } else {
        for (const auto& pattern : result.odcPatterns) {
            Abc_Print(1, "%d%d\n", pattern.first, pattern.second);
        }
    }
    
    return 0;
}

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_sdc", Lsv_CommandSdc, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_odc", Lsv_CommandOdc, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
    PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;