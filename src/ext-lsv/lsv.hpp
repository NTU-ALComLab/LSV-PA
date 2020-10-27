#ifndef LSV_HPP
#define LSV_HPP

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <iostream>
#include <map>

using namespace std;

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);
void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk);
void Lsv_NtkPrintSopunate(Abc_Ntk_t* pNtk);

#endif