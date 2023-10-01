#include "base/main/main.h"
#include "base/main/main.h"
#include "bdd/extrab/extraBdd.h"
#include "base/io/ioAbc.h"
#include "map/mio/mio.h"
#include "bdd/cudd/cuddInt.h"
#include <math.h>
#include <stdint.h>

ABC_NAMESPACE_IMPL_START

int lsv_sim_infolist(Abc_Ntk_t * pNtk);
int lsv_sim_bdd(Abc_Ntk_t * pNtk, char * input_pin);
int lsv_sim_aig(Abc_Ntk_t * pNtk, char * input_filename);

int lsv_sim_infolist_abc(Abc_Frame_t * pAbc) {

    Abc_Ntk_t * pNtk;
    int result;

    pNtk = Abc_FrameReadNtk(pAbc);

    if (pNtk == NULL) {
        Abc_Print(-1, "lsv_sim_infolist_abc: Getting the Target network has failed.\n");
        return 0;
    }

    result = lsv_sim_infolist(pNtk);

    return result;
}

int lsv_sim_bdd_abc(Abc_Frame_t * pAbc, char * input_pin ) {

    Abc_Ntk_t * pNtk;
    int result;

    pNtk = Abc_FrameReadNtk(pAbc);

    if (pNtk == NULL) {
        Abc_Print(-1, "lsv_sim_bdd_abc: Getting the Target network has failed.\n");
        return 0;
    }

    result = lsv_sim_bdd(pNtk, input_pin);

    return result;
}

int lsv_sim_aig_abc(Abc_Frame_t * pAbc, char * input_filename ) {

    Abc_Ntk_t * pNtk;
    int result;

    pNtk = Abc_FrameReadNtk(pAbc);

    if (pNtk == NULL) {
        Abc_Print(-1, "lsv_sim_bdd_abc: Getting the Target network has failed.\n");
        return 0;
    }

    result = lsv_sim_aig(pNtk, input_filename);

    return result;
}

int lsv_sim_infolist(Abc_Ntk_t * pNtk) {
    
    Abc_Print(1, "\t- Abc_NtkIsBddLogic = %d\n", Abc_NtkIsBddLogic(pNtk));
    Abc_Print(1, "\t- Abc_NtkIsBddNetlist = %d\n", Abc_NtkIsBddNetlist(pNtk));
    Abc_Print(1, "\t- Abc_NtkHasBdd = %d\n", Abc_NtkHasBdd(pNtk));

    Abc_Print(1, "The network with name %s has:\n", Abc_NtkName(pNtk));
    Abc_Print(1, "\t- %d primary inputs;\n", Abc_NtkPiNum(pNtk));
    Abc_Print(1, "\t- %d primary outputs;\n", Abc_NtkPoNum(pNtk));
    Abc_Print(1, "\t- %d AND gates;\n", Abc_NtkNodeNum(pNtk));

    int n_input = Abc_NtkPiNum( pNtk );
    int n_output = Abc_NtkPoNum( pNtk );
    int n_node = Abc_NtkNodeNum( pNtk );

    Abc_Obj_t * input_nodes[n_input];
    Abc_Obj_t * output_nodes[n_output];
    Abc_Obj_t * nodes[n_node];

    int i, j, iFanin, new_iFanin;
    Abc_Obj_t * pObj;
    Abc_NtkForEachPi( pNtk, pObj, i ) {
        input_nodes[i] = pObj;
        Abc_Print(1, "\t- input name: %s \n", Abc_ObjName( pObj ));    
        Abc_Print(1, "\t- ID: %d \n", Abc_ObjId( pObj ));
        Abc_Print(1, "\t- number of fanins: %d \n", Abc_ObjFaninNum( pObj ));
        Abc_ObjForEachFaninId( pObj, iFanin, j ) {
            Abc_Print(1, "\t- fanin ids: %d \n", iFanin);
            new_iFanin = Vec_IntFind( &pObj->vFanins, iFanin );
            Abc_Print(1, "\t- fanin nos: %d \n", new_iFanin);
        }
        printf("\n");
    }

    Abc_NtkForEachPo( pNtk, pObj, i ) {
        output_nodes[i] = pObj;
        Abc_Print(1, "\t- output name: %s \n", Abc_ObjName( pObj ));
        Abc_Print(1, "\t- ID: %d \n", Abc_ObjId( pObj ));
        Abc_Print(1, "\t- number of fanins: %d \n", Abc_ObjFaninNum( pObj ));
        Abc_ObjForEachFaninId( pObj, iFanin, j ) {
            Abc_Print(1, "\t- fanin ids: %d \n", iFanin);
            new_iFanin = Vec_IntFind( &pObj->vFanins, iFanin );
            Abc_Print(1, "\t- fanin nos: %d \n", new_iFanin);
        }
        printf("\n");
    }

    Abc_NtkForEachNode( pNtk, pObj, i ) {
        nodes[i] = pObj;
        Abc_Print(1, "\t- node name: %s \n", Abc_ObjName( pObj ));
        Abc_Print(1, "\t- ID: %d \n", Abc_ObjId( pObj ));
        Abc_Print(1, "\t- level: %d \n", Abc_ObjLevel( pObj ));
        Abc_Print(1, "\t- fCompl0: %d \n", pObj->fCompl0 );
        Abc_Print(1, "\t- fCompl1: %d \n", pObj->fCompl1 );
        Abc_Print(1, "\t- number of fanins: %d \n", Abc_ObjFaninNum( pObj ));
        Abc_ObjForEachFaninId( pObj, iFanin, j ) {
            Abc_Print(1, "\t- fanin ids: %d \n", iFanin);
            new_iFanin = Vec_IntFind( &pObj->vFanins, iFanin );
            Abc_Print(1, "\t- fanin nos: %d \n", new_iFanin);
        }
        printf("\n");
    }

    return 0;

}

// This function is inspired from 
// Abc_FlowRetime_SimulateNode in fretInit.c
int lsv_sim_bdd(Abc_Ntk_t * pNtk, char * input_pin) {

    // printf("from lsv_sim_bdd: %s\n", input_pin);

    if ( Abc_NtkIsBddLogic(pNtk) != 1 ) {
        printf("This logic network is not a BDD yet.");
        return 1;
    }
    if ( strlen( input_pin ) != Abc_NtkPiNum( pNtk ) ) {
        printf("Number of bits inputted must be equal to number of network inputs.");
        return 1;
    }
    
    int i, j, rVar ;
    Abc_Obj_t * pPi, * pPo, * pNode, * pFanin;
    DdManager * dd;
    DdNode * pBdd, * pVar;

    
    // printf("List of input names and initial values:\n");

    // For each primary input.
    Abc_NtkForEachPi( pNtk, pPi, i ) {
        // printf("%s: ", Abc_ObjName( pPi ));
        if (input_pin[i] == '0') {
            pPi->fMarkA = 0; // mark as '0' input.
            // printf("%d\n", 0);
        } else if (input_pin[i] == '1') {
            pPi->fMarkA = 1; // mark as '1' input.
            // printf("%d\n", 1);
        } else {
            // printf("All bits must be 0 or 1.");
            return 1;
        }
    }

    // printf("List of output values:\n");*
    
    // For each primary output.
    Abc_NtkForEachPo( pNtk, pPo, i ) {
        dd = pNtk->pManFunc; 
        pNode = Abc_ObjFanin0( pPo ); // a fanin of the output is the bdd object, and is the only one.
        pBdd = pNode->pData;

        // fanins of the pNode is all primary inputs.
        Abc_ObjForEachFanin(pNode, pFanin, j) {
            pVar = Cudd_bddIthVar( dd, j );
            if (pFanin->fMarkA == 0) { // check if the input is 0.
                pBdd = Cudd_Cofactor( dd, pBdd, Cudd_Not(pVar) ); // cofactor w.r.t. input '0'.
            } else { // check if the input is 1.
                pBdd = Cudd_Cofactor( dd, pBdd, pVar ); // cofactor w.r.t. input '1'.
            }
        }
        
        rVar = (pBdd == Cudd_ReadOne(dd)); // check if the output is constant '0' or '1'.
        printf("%s: %d\n", Abc_ObjName( pPo ), rVar); // print the result.
    }

    printf("\n");
    return 0; // no error.
}

int lsv_sim_aig(Abc_Ntk_t * pNtk, char * input_filename) {
    
    // printf("from lsv_sim_aig: %s\n", input_filename);

    //// READ FILE begins.

    FILE * fp;
    char * line = NULL;
    size_t len = 32;
    ssize_t read;
    int PiNum = Abc_NtkPiNum( pNtk );

    fp = fopen(input_filename, "r");
    if (fp == NULL)
        exit(EXIT_FAILURE);
    
    // to store the 32-bits data for each input.
    uint32_t lines[PiNum];
    for (int i = 0; i < PiNum; i++)
    {   
        lines[i] = 0;
    }

    int line_idx = 0;
    while ((read = getline(&line, &len, fp)) != -1) {
        // printf("line_idx = %d\n", line_idx);
        line[strcspn(line, "\n")] = 0; // remove \n.
        // printf("%s\n", line);
        // printf("PiNum = %d\n", PiNum);
        // printf("strlen(line) = %d\n", strlen(line));
        if (strlen(line) != PiNum) {
            printf("Number of bits inputted must be equal to number of network inputs.");
            return 1;
        }

        // store the 32-bits data for each input.
        for (size_t i = 0; i < strlen(line); i++)
        {
            if (line[i] == '\0') {
                continue;
            }
            if (line[i] != '0' && line[i] != '1') {
                printf("The input must be 0 or 1.");
                // printf("%c", line[i]);
                return 1;
            }
            if (line[i] == '1') {
                lines[i] += pow(2, line_idx);
            }
        }
        line_idx += 1;
        if (line_idx > 32) {
            printf("More than 32 bits.");
            return 1;
        }
    }
    printf("\n");

    fclose(fp);
    if (line) free(line);

    //// READ FILE ends.

    /*
    for (size_t i = 0; i < PiNum; i++)
    {
        printf("%d\n", lines[i]);
    }*/

    Vec_Ptr_t * nodes_list;
    nodes_list = Vec_PtrAlloc( Abc_NtkObjNum( pNtk ) ); // for storing each pointer to the node.
    Vec_Ptr_t * logics_list;
    logics_list = Vec_PtrAlloc( Abc_NtkObjNum( pNtk ) ); // for storing 32-bits value at each node.

    int i, j, idx;
    uint32_t logic_tmp, logic_res;
    idx = 0;
    Abc_Obj_t * pObj, * pFanin, * pTemp;

    // for each inputs.
    Abc_NtkForEachPi( pNtk, pObj, i ) {
        Vec_PtrPush( nodes_list, pObj );
        Vec_PtrPush( logics_list, lines[i] );
    }

    // for each nodes.
    Abc_NtkForEachNode( pNtk, pObj, i ) {
        Vec_PtrPush( nodes_list, pObj );
        logic_res = UINT32_MAX; // for storing 11111111111111111111111111111111 (32-bits).

        // for each 2 fanins.
        Abc_ObjForEachFanin( pObj, pFanin, j ) {
            logic_tmp = logics_list->pArray[ Vec_PtrFind( nodes_list, pFanin ) ]; // find the 32-bits value associated to that node.
            if ( Abc_ObjFaninC( pObj, j ) == 1 ) {
                logic_tmp = ~ logic_tmp; // Flip the 32-bits logic of the fanin if it is inverted.
            }
            logic_res = logic_res & logic_tmp; // AND.
        }
        Vec_PtrPush( logics_list, logic_res );
    }

    // for each outputs.
    Abc_NtkForEachPo( pNtk, pObj, i ) {
        Vec_PtrPush( nodes_list, pObj );
        logic_tmp = logics_list->pArray[ Vec_PtrFind( nodes_list, Abc_ObjFanin0( pObj ) ) ]; // an output node has only 1 fanin.
        if ( Abc_ObjFaninC0( pObj ) == 1 ) {
            logic_tmp = ~ logic_tmp; // Flip the 32-bits logic of the fanin if it is inverted.
        }
        Vec_PtrPush( logics_list, logic_tmp );
        
        // print the result
        printf("%s: ", Abc_ObjName( pObj )); 
        for (int i = 0; i < line_idx; ++i) {
            if (logic_tmp >> i & 0x1) putchar('1');
            else putchar('0');
        }
        putchar('\n');
    }

    return 0; // no error.
}




ABC_NAMESPACE_IMPL_END