#ifndef LSV_CUT_H
#define LSV_CUT_H

// This header is needed to define Abc_Ntk_t
#include "base/abc/abc.h"

// We must use extern "C" to ensure C++ name mangling doesn't prevent the C file from finding this function.
#ifdef __cplusplus
extern "C"
{
#endif

    // Declaration of the main C++ function that performs the cut enumeration.
    void Lsv_NtkPrintMoCut(Abc_Ntk_t *pNtk, int k, int l);

#ifdef __cplusplus
}
#endif

#endif // LSV_CUT_H