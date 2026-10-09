#ifndef LSV_CUT_H
#define LSV_CUT_H

#include "base/abc/abc.h"

// Read-only analysis of a structurally hashed AIG. Returns 0 on success.
int Lsv_PrintCuts(Abc_Ntk_t* network, int k, bool bddSize);

#endif
