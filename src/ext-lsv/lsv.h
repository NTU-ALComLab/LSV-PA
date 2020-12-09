#ifndef LSV_H
#define LSV_H

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

extern "C" {
    Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}

void Lsv_NtkPrintUnate(Abc_Ntk_t *pNtk);
void Lsv_NtkPrintUnatePo(Abc_Ntk_t *pNtk);

#endif /* end of include guard: LSV_H */
