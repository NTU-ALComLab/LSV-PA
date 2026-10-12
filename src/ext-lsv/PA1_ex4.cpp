#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
//#include "bdd/cudd/cudd.h"
#include "bdd/extrab/extraBdd.h"

static int Lsv_PA1_Command_cut_tt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_PA1_Command_cut_bddsize(Abc_Frame_t* pAbc, int argc, char** argv);

void init_PA1(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_PA1_Command_cut_tt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_PA1_Command_cut_bddsize, 0);
}

void destroy_PA1(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer_PA1 = {init_PA1, destroy_PA1};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer_PA1); }
} lsv_PA1_PackageRegistrationManager;

void free_vector_of_cuts(Vec_Ptr_t* vec_of_cuts){
    int i;
    Vec_Ptr_t * cut;
    Vec_PtrForEachEntry(Vec_Ptr_t *, vec_of_cuts, cut, i){
        Vec_PtrFree(cut);
    }
    Vec_PtrFree(vec_of_cuts);
}

int NodeIdCompare( const void * pp1, const void * pp2 ) {
    return Abc_ObjId(*(Abc_Obj_t **)pp1) - Abc_ObjId(*(Abc_Obj_t **)pp2);
}

Vec_Ptr_t* get_k_feasible_cuts(Abc_Ntk_t* pNtk, Abc_Obj_t* p_Obj, int k){
    Vec_Ptr_t* cuts = Vec_PtrAlloc(1); 
    Vec_Ptr_t* trivial_cut= Vec_PtrAlloc(1);
    Vec_PtrPush(trivial_cut, p_Obj);
    Vec_PtrPush(cuts, trivial_cut);

    if (k == 1){
        return cuts;
    }
    if (Abc_ObjIsPi(p_Obj)){
        return cuts;
    }
    
    Vec_Ptr_t* cuts_L_Fanin = get_k_feasible_cuts(pNtk, Abc_ObjFanin0(p_Obj), k-1);
    Vec_Ptr_t* cuts_R_Fanin = get_k_feasible_cuts(pNtk, Abc_ObjFanin1(p_Obj), k-1);

    int i, j;
    Vec_Ptr_t * cut_L_F;
    Vec_Ptr_t * cut_R_F;
    Vec_PtrForEachEntry(Vec_Ptr_t *, cuts_L_Fanin, cut_L_F, i){
        Vec_PtrForEachEntry(Vec_Ptr_t *, cuts_R_Fanin, cut_R_F, j){
            Vec_Ptr_t* possible_cut= Vec_PtrAlloc(Vec_PtrSize(cut_L_F) + Vec_PtrSize(cut_R_F));

            int ind;
            Abc_Obj_t* node;
            Vec_PtrForEachEntry(Abc_Obj_t *, cut_L_F, node, ind){
                Vec_PtrPushUnique(possible_cut, node);
            }
            Vec_PtrForEachEntry(Abc_Obj_t *, cut_R_F, node, ind){
                Vec_PtrPushUnique(possible_cut, node);
            }

            if (Vec_PtrSize(possible_cut) <= k){
                Vec_PtrSort(possible_cut, NodeIdCompare);
                
                Vec_PtrPush(cuts, possible_cut);
            }
        }
    }

    
    free_vector_of_cuts(cuts_L_Fanin);
    free_vector_of_cuts(cuts_R_Fanin);

    return cuts;
}


u_int64_t compute_truth_table(Abc_Ntk_t* pNtk, Abc_Obj_t* pObj, Vec_Ptr_t * cut){
    int nb_entry = Vec_PtrSize(cut);
    u_int64_t result = 0;
    
    for (int l=(1 << nb_entry) -1; l >= 0; l--){
        Abc_Obj_t* node_init;
        int m;
        Abc_NtkForEachNode(pNtk, node_init, m) {
            node_init->iTemp = -1;
        }
        Abc_Obj_t* pi_init;
        Abc_NtkForEachPi(pNtk, pi_init, m){
            pi_init->iTemp = -1;
        }        
        
        Vec_Ptr_t* just_computed = Vec_PtrAlloc(1);
        Vec_Ptr_t* left_to_compute = Vec_PtrAlloc(1);
        int i;
        Abc_Obj_t* nodei;
        Vec_PtrForEachEntry(Abc_Obj_t *, cut, nodei, i){
            nodei->iTemp = (l >> (nb_entry-i-1)) % 2;
            Vec_PtrPushUnique(left_to_compute, Abc_ObjFanout0(nodei));
        }
        
        
        while (pObj->iTemp == -1 && Vec_PtrSize(left_to_compute)>0){
            Vec_PtrForEachEntry(Abc_Obj_t *, left_to_compute, nodei, i){
                Abc_Obj_t * nodei_Fanin0 = Abc_ObjFanin0(nodei);
                Abc_Obj_t * nodei_Fanin1 = Abc_ObjFanin1(nodei);
                if (nodei_Fanin0->iTemp==-1 || nodei_Fanin1->iTemp==-1) continue;
                int is_Fanin0_inv = Abc_ObjFaninC0(nodei);
                int is_Fanin1_inv = Abc_ObjFaninC1(nodei);
                int val_Fanin0 = is_Fanin0_inv ? !(nodei_Fanin0->iTemp) : (nodei_Fanin0->iTemp);
                int val_Fanin1 = is_Fanin1_inv ? !(nodei_Fanin1->iTemp) : (nodei_Fanin1->iTemp);
                
                nodei->iTemp = val_Fanin0 && val_Fanin1;
                
                Vec_PtrPush(just_computed, nodei);
            }

            Vec_PtrClear(left_to_compute); 
            Vec_PtrForEachEntry(Abc_Obj_t *, just_computed, nodei, i){
                Vec_PtrPushUnique(left_to_compute, Abc_ObjFanout0(nodei));
            }
        }

        Vec_PtrFree(left_to_compute);
        Vec_PtrFree(just_computed);

        if (pObj->iTemp == -1){ // Impossible case
            printf(" - Error, cannot compute the truth_table - ");
            return 0;
        }

        if (Abc_ObjIsComplement(pObj)) pObj->iTemp = !pObj->iTemp;

        if (pObj->iTemp == 0){
            result = result << 1;
        }
        else {
            result = (result << 1) + 1;
        }
    }
    
    return result;
}


void Lsv_PA1_cut_tt(Abc_Ntk_t* pNtk, int k) {
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {

        Vec_Ptr_t* cuts;
        cuts = get_k_feasible_cuts(pNtk, pObj, k);

        int j;
        Vec_Ptr_t* cut;
        Vec_PtrForEachEntry(Vec_Ptr_t *, cuts, cut, j){
            printf("%d:", Abc_ObjId(pObj));

            int h;
            Abc_Obj_t* node;
            Vec_PtrForEachEntry(Abc_Obj_t *, cut, node, h){
                printf(" %d", Abc_ObjId(node));
            }
            
            u_int64_t tt = compute_truth_table(pNtk, pObj, cut);
            printf(": %lX\n", tt);
        }

        free_vector_of_cuts(cuts);
    }
}




int Lsv_PA1_Command_cut_tt(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int k;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( globalUtilOptind == argc ) 
    {
        Abc_Print(-1, "missing argument k\n" );
        goto usage;
    }
    k = atoi( argv[globalUtilOptind] );

    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    
    Lsv_PA1_cut_tt(pNtk, k);
    
    return 0;


    usage:
    Abc_Print(-2, "usage: lsv_cut_tt <k> [-h]\n");
    Abc_Print(-2, "\t        enumerate all k-feasible cuts of every node on an AIG and print the hexadecimal representation of the cut's truth table\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}



// create a bdd with a cut and return the size
// This function use the CUDD package and I created the BDD by using the same process used to create the truth table in the compute_truth_table function
int create_bdd_cut_size(Abc_Ntk_t* pNtk, Abc_Obj_t* pObj, Vec_Ptr_t * cut){
    Abc_Obj_t* node_init;
    int m;
    Abc_NtkForEachNode(pNtk, node_init, m) {
        node_init->pTemp = nullptr;
    }
    Abc_Obj_t* pi_init;
    Abc_NtkForEachPi(pNtk, pi_init, m){
        pi_init->pTemp = nullptr;
    }
    
    DdManager* bdd_cut = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);

    Vec_Ptr_t* added_to_bdd = Vec_PtrAlloc(1);
    Vec_Ptr_t* left_to_add = Vec_PtrAlloc(1);

    int i;
    Abc_Obj_t* nodei;
    Vec_PtrForEachEntry(Abc_Obj_t *, cut, nodei, i){
        nodei->pTemp = (DdNode *) Cudd_bddIthVar(bdd_cut, i);
        Vec_PtrPushUnique(left_to_add, Abc_ObjFanout0(nodei));
    }

    
    while (pObj->pTemp == nullptr && Vec_PtrSize(left_to_add)>0){
        Vec_PtrForEachEntry(Abc_Obj_t *, left_to_add, nodei, i){
            Abc_Obj_t * nodei_Fanin0 = Abc_ObjFanin0(nodei);
            Abc_Obj_t * nodei_Fanin1 = Abc_ObjFanin1(nodei);

            if (nodei_Fanin0->pTemp==nullptr || nodei_Fanin1->pTemp==nullptr) continue;

            int is_Fanin0_inv = Abc_ObjFaninC0(nodei);
            int is_Fanin1_inv = Abc_ObjFaninC1(nodei);
            
            DdNode* bdd_fanin0 = is_Fanin0_inv ? Cudd_Not((DdNode *) (nodei_Fanin0->pTemp)) : (DdNode *)(nodei_Fanin0->pTemp);
            DdNode* bdd_fanin1 = is_Fanin1_inv ? Cudd_Not((DdNode *) (nodei_Fanin1->pTemp)) : (DdNode *)(nodei_Fanin1->pTemp);
            
            nodei->pTemp = Cudd_bddAnd(bdd_cut, bdd_fanin0, bdd_fanin1);
            Cudd_Ref((DdNode*) (nodei->pTemp));
            
            Vec_PtrPush(added_to_bdd, nodei);
        }

        Vec_PtrClear(left_to_add); 
        Vec_PtrForEachEntry(Abc_Obj_t *, added_to_bdd, nodei, i){
            Vec_PtrPushUnique(left_to_add, Abc_ObjFanout0(nodei));
        }

    }
        
    Vec_PtrFree(left_to_add);
    Vec_PtrFree(added_to_bdd);

    if (pObj->pTemp == nullptr){ // Impossible case
        printf(" - Error, cannot compute the BDD - ");
        return 0;
    }

    int result = Cudd_DagSize((DdNode *) (pObj->pTemp));

    Cudd_RecursiveDeref(bdd_cut, (DdNode *) (pObj->pTemp));
    Cudd_Quit(bdd_cut);

    return result;
}

void Lsv_PA1_cut_bddsize(Abc_Ntk_t* pNtk, int k) {
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {

        Vec_Ptr_t* cuts;
        cuts = get_k_feasible_cuts(pNtk, pObj, k);


        int j;
        Vec_Ptr_t* cut;
        Vec_PtrForEachEntry(Vec_Ptr_t *, cuts, cut, j){
            printf("%d:", Abc_ObjId(pObj));

            int h;
            Abc_Obj_t* node;
            Vec_PtrForEachEntry(Abc_Obj_t *, cut, node, h){
                printf(" %d", Abc_ObjId(node));
            }
            
            int size_bdd = create_bdd_cut_size(pNtk, pObj, cut);
        
            printf(": %d\n", size_bdd);
        }

        free_vector_of_cuts(cuts);
    }

}

int Lsv_PA1_Command_cut_bddsize(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c;
    int k;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( globalUtilOptind == argc ) 
    {
        Abc_Print(-1, "missing argument k\n" );
        goto usage;
    }
    k = atoi( argv[globalUtilOptind] );

    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    
    Lsv_PA1_cut_bddsize(pNtk, k);
    
    return 0;


    usage:
    Abc_Print(-2, "usage: lsv_cut_bddsize <k> [-h]\n");
    Abc_Print(-2, "\t        enumerate all k-feasible cuts of every node on an AIG, generate corresponding ROBDD for each cut, and print the BDD size\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}