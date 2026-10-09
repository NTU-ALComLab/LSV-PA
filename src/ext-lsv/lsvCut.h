#ifndef LSV_CUT_H
#define LSV_CUT_H

#include "base/abc/abc.h"

#include <cstdint>
#include <vector>

typedef std::vector<int> Lsv_Cut;
typedef std::vector<Lsv_Cut> Lsv_Cuts;

// The caller sizes both caches to Abc_NtkObjNumMax(pNtk).
const Lsv_Cuts& Lsv_EnumerateCuts(Abc_Obj_t* pObj, int k,
                                 std::vector<Lsv_Cuts>& cuts,
                                 std::vector<bool>& done);
uint64_t Lsv_TruthMask(unsigned n);
uint64_t Lsv_CutTruth(Abc_Obj_t* pObj, const Lsv_Cut& cut);
int Lsv_NtkCutTt(Abc_Ntk_t* pNtk, int k);
int Lsv_NtkCutBddSize(Abc_Ntk_t* pNtk, int k);

#endif
