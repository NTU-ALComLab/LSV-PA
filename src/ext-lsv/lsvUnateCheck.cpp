#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include "bdd/cudd/cuddInt.h"

#include "sat/cnf/cnf.h"
extern "C"{
    Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

#include <string>

// STL related
#include <vector>
#include <set>
#include <unordered_set>
#include <map>
#include <unordered_map>


// Problem 1: Unateness check on BDD
// =============================================================================
void Lsv_CommandUnateBDDUsage(){
    Abc_Print(-2, "Usage: lsv_unate_bdd <out_index> <in_index>\n");
    Abc_Print(-2, "\tchecks unate property of a BDD output with respect to an input\n");
    Abc_Print(-2, "\t<out_index>     : the index of the output to be checked\n");
    Abc_Print(-2, "\t<in_index>      : the index of the input to be checked\n");
}

// Determine if the BDD node is the constant 0 node
inline bool isNodeZero(DdManager *dd, DdNode *node){
    return (node == DD_ZERO(dd)) || (node == Cudd_Not(DD_ONE(dd)));
}

// Determine if the BDD node is the constant 1 node
inline bool isNodeOne(DdManager *dd, DdNode *node){
    return (node == DD_ONE(dd)) || (node == Cudd_Not(DD_ZERO(dd)));
}

// ==============================================================
// NOTE:
//      In CUDD, BDD are "complemented edges" representation.
//      (See the slides P.51, lecture 2)
//      The BDD node pointer has the last bit set to indicate 
//      if the edge is inverted. Use Cudd_Regular to get 
//      the actual node address.
//      Therefore, CONSTANT 0 and CONSTANT 1 share the same node,
//      but the node "addresses" are different in the last bit.
// ==============================================================

// Depth-First Search (DFS) to traverse the BDD and collect paths
void Lsv_UnateBDD_DFS(DdManager *dd, DdNode *node,
                      std::vector<int> &current_path,
                      const int bottom_level_index,
                      std::vector<std::vector<int>> &all_paths,
                      std::unordered_map<DdNode *, int> &visited_nodes,
                      const bool visit_type_last,       // 0: visit normal function, 1: visit complemented function
                      bool &positive_witness,
                      bool &negative_witness,
                      bool &positive_witness_first){
    
    // printf("\n");

    // ==============================================================
    // NOTE:
    //    Assume the current node funtion is f
    // ==============================================================

    // The last bit indicates if the edge is inverted; if inverted, the last bit is 1
    const bool edge_inverted = Cudd_IsComplement(node);

    // Determine the visit type for the current node (visit f (= false) or ~f (= true))
    const bool visit_type_current = visit_type_last ^ edge_inverted;  

    // Remove the last bit (set it to 0), get the regular node address
    node = Cudd_Regular(node);
    
    if (Cudd_IsConstant(node)){
        // printf("PASS constant\n");
        return;
    }

    // printf("Current node index: %p\n", node);

    // ==============================================================
    // NOTE:
    //   visited_nodes:
    //       NO Mapping : not visited
    //               0  : visited f
    //               1  : visited ~f (not f)
    //               2  : visited both f and ~f
    // ==============================================================

    auto it = visited_nodes.find(node);
    if (it == visited_nodes.end()){             // Does not visited before
        visited_nodes[node] = visit_type_current ? 1 : 0;
    }
    else if (it -> second == 0){                  // Visited f before
        if (visit_type_current){                  // Now visit ~f
            visited_nodes[node] = 2;              // Visited both
        }
        else{                                     // Now visit f again
            // printf("PASS visited f again\n");
            return;
        }
    }
    else if (it -> second == 1){                  // Visited ~f before
        if (!visit_type_current){                 // Now visit f
            visited_nodes[node] = 2;              // Visited both
        }
        else{                                     // Now visit ~f again
            // printf("PASS visited ~f again\n");
            return;
        }
    }
    else{                                         // Visited both before
        // printf("PASS visited both before\n");
        return;
    }

    DdNode *zero_child = Cudd_E(node); // Else child
    DdNode *one_child = Cudd_T(node);  // Then child

    // printf("LEFT child ptr address: %p\n", zero_child);
    // printf("RIGHT child ptr address: %p\n", one_child);

    int index = Cudd_NodeReadIndex(node);
    // printf("Visiting node with index: %d\n", index);

    // If it is the most bottom variable
    if (index == bottom_level_index){
        // printf("Bottom level variable reached\n");
        // printf("Bottom level index: %d\n", bottom_level_index);
        // printf("Before: %d %d\n", positive_witness, negative_witness);
        if (!visit_type_current){
            // positive witness found
            // printf("Positive witness found\n");
            positive_witness = true;
            if (size(all_paths) == 0){
                positive_witness_first = true;
            }
        }
        else{
            // negative witness found
            // printf("Negative witness found\n");
            negative_witness = true;
        }

        // printf("Zero child index: %d\n", Cudd_NodeReadIndex(zero_child));
        // printf("One child index: %d\n", Cudd_NodeReadIndex(one_child));

        // printf("After: %d %d\n", positive_witness, negative_witness);

        // Hard copy the current path to the all_paths
        std::vector<int> path_copy = current_path;
        all_paths.push_back(path_copy);
        return;
    }

    // printf("Left children of node %p\n", node);
    current_path[index] = 0;
    Lsv_UnateBDD_DFS(dd, zero_child, current_path, bottom_level_index, all_paths, visited_nodes, visit_type_current, positive_witness, negative_witness, positive_witness_first);

    // printf("\n");
    // printf("Right children of node %p\n", node);
    current_path[index] = 1;
    Lsv_UnateBDD_DFS(dd, one_child, current_path, bottom_level_index, all_paths, visited_nodes, visit_type_current, positive_witness, negative_witness, positive_witness_first);
}

int Lsv_CommandUnateBDD(Abc_Frame_t *pAbc, int argc, char **argv){
    // printf("LSV Command lsv_unate_bdd is called.\n");

    // Step 1: Argument parsing and checking
    // =======================================================
    if (argc != 3){
        Lsv_CommandUnateBDDUsage();
        return 0;
    }

    const int out_index = std::stoi(argv[1]);
    const int in_index = std::stoi(argv[2]);

    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);

    if (!Abc_NtkIsBddLogic(pNtk)){
        Abc_Print(-1, "The network is not in BDD logic representation. Should perform \"collapse\" after reading the design.\n");
        return 0;
    }

    const int pi_num = Abc_NtkPiNum(pNtk);
    const int po_num = Abc_NtkPoNum(pNtk);

    if (in_index >= pi_num){
        Abc_Print(-1, "input index exceeds the number of PIs.\n");
        return 0;
    }

    if (out_index >= po_num){
        Abc_Print(-1, "output index exceeds the number of POs.\n");
        return 0;
    }

    // Step 2: Get the BDD manager
    // =======================================================
    Abc_Obj_t *_po = Abc_NtkPo(pNtk, out_index);
    Abc_Obj_t *pRoot = Abc_ObjFanin0(_po);
    DdManager *dd = (DdManager *)pNtk->pManFunc;
    DdNode *f = (DdNode *)pRoot->pData;

    // Testing functionality
    // printf("Testing\n");
    // for (int i = 0; i < Abc_NtkPoNum(pNtk); i++){
    //     Abc_Obj_t* _po_iter = Abc_NtkPo(pNtk, i);
    //     Abc_Obj_t* pRoot_iter = Abc_ObjFanin0(_po_iter);
    //     DdNode* f_iter = (DdNode *) pRoot_iter -> pData;
    //     // Cudd_Ref(f_iter);
    //     printf("PO %d BDD node address: %d\n", i, Cudd_NodeReadIndex(f_iter));
    //     printf("PO %d BDD node index: %d\n", i, Cudd_NodeReadIndex(Cudd_E(f_iter)));
    //     printf("PO %d BDD node index: %d\n", i, Cudd_NodeReadIndex(Cudd_T(f_iter)));

    //     if (i == 1){
    //         printf("Special index: %d\n", Cudd_NodeReadIndex(Cudd_T(Cudd_E(Cudd_T(Cudd_T(f_iter))))));
    //     }
    //     // Cudd_RecursiveDeref(dd, f_iter);
    // }

    // assert(pNtk == (pRoot -> pNtk));

    // Step 3: Construct Mapping between PI_index and BDD order
    // =======================================================
    // pi_name_to_index[PI_NAME] = PI_INDEX
    std::unordered_map<std::string, int> pi_name_to_index;
    Abc_Obj_t *_pi;
    int i = 0;
    Abc_NtkForEachPi(pNtk, _pi, i){
        pi_name_to_index[Abc_ObjName(_pi)] = i;
    }

    // Consider the support of f, and the order is the BDD order
    Vec_Ptr_t *support_f_Names = Abc_NodeGetFaninNames(pRoot);
    char **support_f_Names_arr = (char **)Vec_PtrArray(support_f_Names);
    int support_f_size = Vec_PtrSize(support_f_Names);

    // printf("Support of the function at PO #%d:\n", out_index);
    // for (int i = 0; i < support_f_size; i++){
    //     printf("Support variable %d: %s\n", i, support_f_Names_arr[i]);
    // }

    // The BDD level of the designated input variable
    int in_bdd_level = -1;
    for (int i = 0; i < support_f_size; i++){
        if (strcmp(support_f_Names_arr[i], Abc_ObjName(Abc_NtkPi(pNtk, in_index))) == 0){
            // printf("The input PI #%d is at BDD level %d\n", in_index, i);
            in_bdd_level = i;
        }
    }

    if (in_bdd_level == -1){
        printf("independent\n");
        return 0;
    }

    // Step 4: Shuffle the input variable to the bottom
    // =======================================================
    // printf("Support size: %d\n", support_f_size);
    int n = Cudd_ReadSize(dd);
    int *perm = (int*)malloc(sizeof(int) * n);

    for (int level = 0; level < n; level++){
        perm[level] = level;
    }

    // Change the original position of in_bdd_level to the last position
    perm[support_f_size - 1] = in_bdd_level;
    perm[in_bdd_level] = support_f_size - 1;

    // print perm array
    // printf("Permutation array:\n");
    // for (int level = 0; level < support_f_size; level++){
    //     printf("Level %d -> Var %d\n", level, perm[level]);
    // }

    // for (int level = 0; level < n; ++level) {
    //     int index = Cudd_ReadInvPerm(dd, level);
    //     printf("BF: Level %d -> Var %d\n", level, index);
    // }

    Cudd_ShuffleHeap(dd, perm);

    // for (int level = 0; level < n; ++level) {
    //     int index = Cudd_ReadInvPerm(dd, level);
    //     printf("AT: Level %d -> Var %d\n", level, index);
    // }

    free(perm);

    // Step 5: DFS traversal to collect all paths
    // =====================================================
    std::vector<std::vector<int>> all_paths;
    std::vector<int> current_path(support_f_size, 0);
    std::unordered_map<DdNode *, int> visited_nodes;
    bool positive_witness = false;
    bool negative_witness = false;
    bool positive_witness_first = false;
    Lsv_UnateBDD_DFS(dd, f, current_path, in_bdd_level, all_paths, visited_nodes, false, positive_witness, negative_witness, positive_witness_first);

    // Step 6: print the result
    // =====================================================
    // printf("=========================================================\n");
    if (size(all_paths) == 0){
        printf("independent\n");
    }
    else if (positive_witness && !negative_witness){
        printf("positive unate\n");
    }
    else if (!positive_witness && negative_witness){
        printf("negative unate\n");
    }
    else{
        printf("binate\n");

        std::vector<int> pos_example(Abc_NtkPiNum(pNtk), 0);
        std::vector<int> neg_example(Abc_NtkPiNum(pNtk), 0);

        // printf("Size of all_paths: %d\n", size(all_paths));

        // printf("===========================================================\n");
        // printf("ALL_PATHS_DETAILS:\n");
        // for (int i = 0; i < size(all_paths); i++){
        //     printf("Path %d: ", i);
        //     for (int j = 0; j < support_f_size; j++){
        //         printf("%d", all_paths[i][j]);
        //     }
        //     printf("\n");
        // }
        // printf("===========================================================\n");

        if (positive_witness_first){
            // printf("POS witness first\n");
            for (int i = 0; i < support_f_size; i++){
                int pi_index = pi_name_to_index[support_f_Names_arr[i]];
                pos_example[pi_index] = all_paths[0][i];
            }

            for (int i = 0; i < support_f_size; i++){
                int pi_index = pi_name_to_index[support_f_Names_arr[i]];
                neg_example[pi_index] = all_paths[1][i];
            }
        }
        else{
            // printf("NEG witness first\n");
            for (int i = 0; i < support_f_size; i++){
                int pi_index = pi_name_to_index[support_f_Names_arr[i]];
                neg_example[pi_index] = all_paths[0][i];
            }

            for (int i = 0; i < support_f_size; i++){
                int pi_index = pi_name_to_index[support_f_Names_arr[i]];
                pos_example[pi_index] = all_paths[1][i];
            }
        }

        // Don't-care
        pos_example[pi_name_to_index[support_f_Names_arr[in_bdd_level]]] = -1;
        neg_example[pi_name_to_index[support_f_Names_arr[in_bdd_level]]] = -1;

        // Print positive example
        for (int i = 0; i < Abc_NtkPiNum(pNtk); i++){
            if (pos_example[i] == -1){
                printf("-");
            }
            else{
                printf("%d", pos_example[i]);
            }
        }
        printf("\n");

        // Print negative example
        for (int i = 0; i < Abc_NtkPiNum(pNtk); i++){
            if (neg_example[i] == -1){
                printf("-");
            }
            else{
                printf("%d", neg_example[i]);
            }
        }
        printf("\n");
    }

    // Abc_Print(-2, "END\n");
    // printf("=========================================================\n");
    return 0;
}



// Problem 2: Unateness check on BDD
// =============================================================================

void Lsv_CommandUnateSATUsage(){
    Abc_Print(-2, "Usage: lsv_unate_sat <out_index> <in_index>\n");
    Abc_Print(-2, "\tchecks unate property of a AIG output with respect to an input\n");
    Abc_Print(-2, "\t<out_index>     : the index of the output to be checked\n");
    Abc_Print(-2, "\t<in_index>      : the index of the input to be checked\n");
}

int Lsv_CommandUnateSAT(Abc_Frame_t *pAbc, int argc, char **argv){
    // printf("LSV Command lsv_unate_sat is called.\n");

    // Step 1: Argument parsing and checking
    // =======================================================
    if (argc != 3){
        Lsv_CommandUnateSATUsage();
        return 0;
    }

    const int out_index = std::stoi(argv[1]);
    const int in_index = std::stoi(argv[2]);

    Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);

    if (!Abc_NtkIsStrash(pNtk)){
        Abc_Print(-1, "The network is not in AIG logic representation. Should perform \"strash\" after reading the design.\n");
        return 0;
    }

    const int pi_num = Abc_NtkPiNum(pNtk);
    const int po_num = Abc_NtkPoNum(pNtk);

    if (in_index >= pi_num){
        Abc_Print(-1, "input index exceeds the number of PIs.\n");
        return 0;
    }

    if (out_index >= po_num){
        Abc_Print(-1, "output index exceeds the number of POs.\n");
        return 0;
    }


    // Step 2: Extract desired output cone
    // =======================================================
    
    // Extract the cone
    Abc_Obj_t* output_obj = Abc_NtkPo(pNtk, out_index);
    Abc_Ntk_t* cone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(output_obj), Abc_ObjName(output_obj), 1);

    // DEBUG for SOOOO LONGGGG
    // I don't know what the xxxx ?????
    // when extracting cone, make sure whether it is complmemented.
    int _isCompl = Abc_ObjFaninC0(output_obj);
    bool isCompl = (_isCompl == 1) ? true : false;

    // Transform cone to AIG
    Aig_Man_t* pAig = Abc_NtkToDar(cone, 0, 1);
    
    // Transfer AIG to CNF
    Cnf_Dat_t* pCnf = Cnf_Derive(pAig, 1);         // 1: the number of outputs


    // Step 3: Build the SAT solver instance and solve the result
    // =======================================================
    bool find_postive_instance_successful, find_negative_instance_successful;
    find_postive_instance_successful = false;
    find_negative_instance_successful = false;

    std::vector<int> positive_instance(pi_num, 0);
    std::vector<int> negative_instance(pi_num, 0);

    for (int sat_solve_cnt = 0; sat_solve_cnt < 2; sat_solve_cnt++){

        sat_solver* pSat = sat_solver_new();
        
        // When sat_solve_cnt == 0, we are finding positive instance (input changes from 0 to 1 makes output change from 0 to 1)
        // When sat_solve_cnt == 1, we are finding negative instance (input changes from 0 to 1 makes output change from 1 to 0)
        bool find_postive_instance;
        find_postive_instance = (sat_solve_cnt == 0) ? true : false;

        // Step 3-1: Add the circuit into the CNF
        // =======================================================
        // Add two copies (A, B) of the circuit into the SAT solver
        // vA(0, 1, ..., n-1)
        pSat = (sat_solver *) Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
        Cnf_DataLift(pCnf, pCnf -> nVars);
        // vB(0, 1, ..., n-1)
        pSat = (sat_solver *) Cnf_DataWriteIntoSolverInt(pSat, pCnf, 2, 0);
        Cnf_DataLift(pCnf, -1 * pCnf -> nVars);
        // pSat = (sat_solver *) Cnf_DataWriteIntoSolverInt(pSat, pCnf, 2, 0);

        
        // Step 3-2 Adding other constraint to the SAT solver
        // =======================================================
        int clause[2];
        
        Aig_Obj_t* pObj;
        int index;
        
        // Set all variable to be equal in two cases, except the designated input
        Aig_ManForEachCi(pAig, pObj, index){
            if (index != in_index){
                // Add vA(i) == vB(i) => (vA(i) + vB(i)') and (vA(i)' + vB(i))
                clause[0] = toLitCond(pCnf -> pVarNums[pObj -> Id], 0);
                clause[1] = toLitCond(pCnf -> pVarNums[pObj -> Id] + pCnf -> nVars, 1);
                sat_solver_addclause(pSat, clause, clause + 2);

                clause[0] = toLitCond(pCnf -> pVarNums[pObj -> Id], 1);
                clause[1] = toLitCond(pCnf -> pVarNums[pObj -> Id] + pCnf -> nVars, 0);
                sat_solver_addclause(pSat, clause, clause + 2);
            }
            else {
                // vA(in_index) = 0 (vA(in_index)')
                clause[0] = toLitCond(pCnf -> pVarNums[pObj -> Id], 1);
                sat_solver_addclause(pSat, clause, clause + 1);
                
                // vB(in_index) = 1 (vB(in_index))
                clause[0] = toLitCond(pCnf -> pVarNums[pObj -> Id] + pCnf -> nVars, 0);
                sat_solver_addclause(pSat, clause, clause + 1);
            }
        }

        // Set the output condition
        Aig_ManForEachCo(pAig, pObj, index){
            if (find_postive_instance){
                // Positive instance: vA(output) = 0, vB(output) = 1
                // vA(output)' 
                clause[0] = toLitCond(pCnf -> pVarNums[pObj -> Id], isCompl ? 0 : 1);
                sat_solver_addclause(pSat, clause, clause + 1);

                // vB(output)
                clause[0] = toLitCond(pCnf -> pVarNums[pObj -> Id] + pCnf -> nVars, isCompl ? 1 : 0);
                sat_solver_addclause(pSat, clause, clause + 1);
            }
            else{
                // Negative instance: vA(output) = 1, vB(output) = 0
                // vA(output)
                clause[0] = toLitCond(pCnf -> pVarNums[pObj -> Id], isCompl ? 1 : 0);
                sat_solver_addclause(pSat, clause, clause + 1);

                // vB(output)'
                clause[0] = toLitCond(pCnf -> pVarNums[pObj -> Id] + pCnf -> nVars, isCompl ? 0 : 1);
                sat_solver_addclause(pSat, clause, clause + 1);
            }
        }


        // Step 3-3: Solve SAT
        // =======================================================
        int status = sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);

        if (status == l_Undef){
            Abc_Print(-1, "SAT cannot solve it!\n");
            return 0;
        }
        else if (status == l_False){ // UNSAT
            // printf("UNSAT\n");
            // Do nothing
        }
        else if (status == l_True){     // SAT
            if (find_postive_instance){
                find_postive_instance_successful = true;

                // Extract the positive instance
                Aig_ManForEachCi(pAig, pObj, index){
                    positive_instance[index] = sat_solver_var_value(pSat, pCnf -> pVarNums[pObj -> Id]);
                    negative_instance[index] = sat_solver_var_value(pSat, pCnf -> pVarNums[pObj -> Id] + pCnf -> nVars);
                }
            }
            else{
                find_negative_instance_successful = true;

                // Extract the negative instance
                Aig_ManForEachCi(pAig, pObj, index){
                    negative_instance[index] = sat_solver_var_value(pSat, pCnf -> pVarNums[pObj -> Id]);
                }
            }
        }
    }


    // Step 4: Output the result
    // =======================================================
    if (!find_postive_instance_successful && !find_negative_instance_successful){
        printf("independent\n");
    }
    else if (find_postive_instance_successful && !find_negative_instance_successful){
        printf("positive unate\n");
    }
    else if (!find_postive_instance_successful && find_negative_instance_successful){
        printf("negative unate\n");
    }
    else{
        printf("binate\n");

        for (int i = 0; i < pi_num; i++){
            if (i == in_index){
                printf("-");   // don't care
            }
            else{
                printf("%d", positive_instance[i]);
            }
        }
        printf("\n");

        for (int i = 0; i < pi_num; i++){
            if (i == in_index){
                printf("-");   // don't care
            }
            else{
                printf("%d", negative_instance[i]);
            }
        }
        printf("\n");
    }

    return 0;
}