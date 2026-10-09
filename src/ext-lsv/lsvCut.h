#ifndef LSV_CUT_H
#define LSV_CUT_H

#include "base/abc/abc.h"

// Enumerate k-feasible cuts of every internal AND and print truth tables.
void Lsv_PrintCutTruth(Abc_Ntk_t* pNtk, int k);

// Same cuts, printing the ROBDD node count of each cut.
void Lsv_PrintCutBddSize(Abc_Ntk_t* pNtk, int k);

#endif
