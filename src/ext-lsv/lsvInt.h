#ifndef ABC__ext_lsv__lsvInt_h
#define ABC__ext_lsv__lsvInt_h

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

ABC_NAMESPACE_HEADER_START

int Lsv_CommandUnateBdd(Abc_Frame_t *pAbc, int argc, char **argv);
int Lsv_CommandUnateSat(Abc_Frame_t *pAbc, int argc, char **argv); // For Task 2

ABC_NAMESPACE_HEADER_END

#endif