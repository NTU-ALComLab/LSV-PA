#ifndef LSV_CMD_H
#define LSV_CMD_H

#include <vector>
#include <string>
#include <cassert>
#include <queue>
#include <unordered_map>
#include "base/abc/abc.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver2.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "ext-lsv/lsv_struct.h"

namespace lsv
{

int CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
int CommandPrintSOPUnate(Abc_Frame_t* pAbc, int argc, char** argv);
int CommandPrintPOUnate(Abc_Frame_t* pAbc, int argc, char** argv);

}   /// end of namespace lsv

#endif
