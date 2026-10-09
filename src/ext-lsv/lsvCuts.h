#ifndef ABC_EXT_LSV_CUTS_H
#define ABC_EXT_LSV_CUTS_H

#include "base/abc/abc.h"

#include <vector>

typedef std::vector<int> Lsv_Cut;
typedef std::vector<Lsv_Cut> Lsv_CutList;
typedef std::vector<Lsv_CutList> Lsv_AllCuts;

const Lsv_CutList& Lsv_ComputeCuts(
    Abc_Obj_t* pObj,
    int k,
    Lsv_AllCuts& allCuts,
    std::vector<char>& computed);

#endif
