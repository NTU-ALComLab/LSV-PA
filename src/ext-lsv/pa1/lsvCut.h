#ifndef LSV_PA1_LSVCUT_H
#define LSV_PA1_LSVCUT_H

#include <cstdint>
#include <vector>

#include "base/abc/abc.h"
// For ptrint, which the Cudd_Not macro needs. Do not use extraBdd.h:
// it defines a0/a1/b0/b1 as macros.
#include "bdd/cudd/cuddInt.h"

// Leaf IDs in ascending order.
typedef std::vector<int> Lsv_Cut_t;

// All cuts of one node, trivial cut first.
typedef std::vector<Lsv_Cut_t> Lsv_CutSet_t;

// out = a U b, or 0 if that needs more than k leaves.
int Lsv_CutUnion(const Lsv_Cut_t& a, const Lsv_Cut_t& b, int k, Lsv_Cut_t& out);

int Lsv_CutSetHas(const Lsv_CutSet_t& set, const Lsv_Cut_t& cut);

void Lsv_NtkEnumCuts(Abc_Ntk_t* pNtk, int k, std::vector<Lsv_CutSet_t>& cuts);

// Leaf 0 is the most significant variable.
uint64_t Lsv_CutTruth(Abc_Obj_t* pRoot, const Lsv_Cut_t& cut);

// Leaf j becomes CUDD variable j.
int Lsv_CutBddSize(DdManager* dd, Abc_Obj_t* pRoot, const Lsv_Cut_t& cut);

#endif
