#ifndef LSV_H
#define LSV_H

#include "base/abc/abc.h"
#include "base/main/main.h" // Required for Abc_Frame_t

#ifdef __cplusplus
extern "C" {
#endif

// Registration (called by ext loader)
void Lsv_Init(Abc_Frame_t* pAbc);
void Lsv_End(Abc_Frame_t* pAbc);

// PA2 Part 1: BDD unateness command
int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv);

// PA2 Part 2: SAT unateness command
int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv);

#ifdef __cplusplus
}
#endif

#endif // LSV_H
