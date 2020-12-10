#ifndef __ABC_EXT_LSV_UTILS_H__
#define __ABC_EXT_LSV_UTILS_H__

#include <vector>
#include "base/abc/abc.h"

bool Lsv_CmpAbcObjId(Abc_Obj_t& a, Abc_Obj_t& b);
void Lsv_UtilPrintAbcObjVecs(std::vector<Abc_Obj_t> &vec);

#endif
