#ifndef ABC__ext_lsv__lsvPA_h
#define ABC__ext_lsv__lsvPA_h

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#define UNKNOWN 0
#define POSUNATE 1
#define NEGUNATE 2
#define BINATE 3

int Lsv_NtkPrintSopUnate(Abc_Ntk_t *pNtk);

#endif