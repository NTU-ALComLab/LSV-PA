#ifndef TESTFIRST_h
#define TESTFIRST_h

#include "base/main/main.h"

ABC_NAMESPACE_IMPL_START

extern int lsv_sim_infolist_abc(Abc_Frame_t * pAbc);
extern int lsv_sim_bdd_abc(Abc_Frame_t * pAbc, char * input_pin);
extern int lsv_sim_aig_abc(Abc_Frame_t * pAbc, char * input_filename);

#endif

ABC_NAMESPACE_IMPL_END