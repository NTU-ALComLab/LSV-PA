#ifndef LSV_CUT_H
#define LSV_CUT_H

#include "base/main/main.h"

// Q4 command entry points for ABC; cut data and algorithms are private to lsvCut.cpp.
int Lsv_CommandCutTt(Abc_Frame_t* frame, int argc, char** argv);
int Lsv_CommandCutBddSize(Abc_Frame_t* frame, int argc, char** argv);

#endif
