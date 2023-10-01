#include "base/main/main.h"
#include "lsv_sim.h"

ABC_NAMESPACE_HEADER_START

extern int lsv_sim_infolist_cmd(Abc_Frame_t * pAbc, int argc, char ** argv);
extern int lsv_sim_bdd_cmd(Abc_Frame_t * pAbc, int argc, char ** argv);
extern int lsv_sim_aig_cmd(Abc_Frame_t * pAbc, int argc, char ** argv);

void lsv_sim_init(Abc_Frame_t * pAbc) {
    Cmd_CommandAdd(pAbc, "Various", "lsv_sim_infolist", lsv_sim_infolist_cmd, 0);
    Cmd_CommandAdd(pAbc, "Various", "lsv_sim_bdd", lsv_sim_bdd_cmd, 0);
    Cmd_CommandAdd(pAbc, "Various", "lsv_sim_aig", lsv_sim_aig_cmd, 0);
}

int lsv_sim_infolist_cmd(Abc_Frame_t * pAbc, int argc, char ** argv) {
    
    int result;

    result = lsv_sim_infolist_abc(pAbc);

    return 0;

usage:
}

int lsv_sim_bdd_cmd(Abc_Frame_t * pAbc, int argc, char ** argv) {

    int result;

    char * input_pin = argv[1];

    // printf("from lsv_sim_bdd_cmd: %s\n", input_pin);
    
    result = lsv_sim_bdd_abc( pAbc, input_pin );

    return 0;

usage:
}

int lsv_sim_aig_cmd(Abc_Frame_t * pAbc, int argc, char ** argv) {

    int result;

    char * input_filename = argv[1];

    // printf("from lsv_sim_aig_cmd: %s\n", input_filename);
    
    result = lsv_sim_aig_abc( pAbc, input_filename );

    return 0;

usage:
}

ABC_NAMESPACE_HEADER_END