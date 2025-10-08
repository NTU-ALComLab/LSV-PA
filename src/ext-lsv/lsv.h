#ifndef LSV_H
#define LSV_H

#include "base/abc/abc.h"

#ifdef __cplusplus
extern "C" {
#endif

// Registration (called by ext loader)
void Lsv_Init(Abc_Frame_t* pAbc);
void Lsv_End(Abc_Frame_t* pAbc);

#ifdef __cplusplus
}
#endif

#endif // LSV_H
