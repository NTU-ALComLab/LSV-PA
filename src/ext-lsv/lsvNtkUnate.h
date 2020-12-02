#ifndef ABC__ext_lsv__lsvPA_h
#define ABC__ext_lsv__lsvPA_h

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"

#define UNKNOWN 0
#define POSUNATE 1
#define NEGUNATE 2
#define BINATE 3

// PA1
int Lsv_NtkPrintSopUnate(Abc_Ntk_t *pNtk);
void printNodeUnate(char *name, Abc_Ntk_t *pNtk, Vec_Int_t *punate, Vec_Int_t *nunate, Vec_Int_t *binate);

// PA2
int Lsv_NtkPrintPoUnate(Abc_Ntk_t *pNtk);
void addCnfClauses(sat_solver *pSat, Cnf_Dat_t *pCnf);
int proofUnate(Aig_Man_t *pMan, sat_solver *pSat, Cnf_Dat_t *pCnfPos, Cnf_Dat_t *pCnfNeg, int po, int pi, int *alphas, int flag);

extern "C"
{
    Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
}

#endif