#ifndef LSV_CMD_H
#define LSV_CMD_H

#include <iostream>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv);

#endif