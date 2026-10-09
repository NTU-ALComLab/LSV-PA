#ifndef LSV_CUT_H
#define LSV_CUT_H

#include "base/abc/abc.h"
#include <cstdint>
#include <vector>

#ifdef ABC_USE_CUDD
#include "bdd/cudd/cudd.h"
#endif

using Cut = std::vector<int>;          // leaf in a cut
using CutList = std::vector<Cut>;      // cuts of a node
using CutTable = std::vector<CutList>; // all cuts of all nodes in a network

bool mergeCuts(const Cut &left, const Cut &right, int k, Cut &result);

bool enumerateCuts(Abc_Ntk_t *pNtk, int k, CutTable &cuts);

bool evaluate(Abc_Obj_t *node, const Cut &cut, unsigned assignment);

std::uint64_t computeTruthTable(Abc_Obj_t *root, const Cut &cut);

#ifdef ABC_USE_CUDD

DdNode *buildBdd(DdManager *manager, std::uint64_t truth,
                 int remainingVariables, int variableIndex);
#endif

bool Lsv_RunCutTruthTables(Abc_Ntk_t *pNtk, int k);
bool Lsv_RunCutBddSizes(Abc_Ntk_t *pNtk, int k);

#endif
