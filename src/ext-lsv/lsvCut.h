#ifndef LSV_CUT_H
#define LSV_CUT_H

#include "base/abc/abc.h"
#include "bdd/cudd/cudd.h"

#include <cstdint>
#include <map>
#include <vector>

// ===================== PA1 4.1: k-feasible cuts =====================

// A cut of a node
struct Cut
{
  std::vector<int> leaves; // leaf node IDs in ascending order
  uint64_t sign = 0;       // signature: each leaf sets bit (ID % 64); used to reject oversized merges early

  bool operator<(const Cut &o) const { return leaves < o.leaves; } // ordering for std::set (duplicate check)
};

typedef std::map<int, std::vector<Cut>> CutTable; // cuts[ID] = all cuts of that node

// Union of two sorted cuts (sorted, no duplicates); the result is written to u
void Lsv_CutMerge(const Cut &a, const Cut &b, Cut &u);

// Enumerate all k-feasible cuts of every node bottom-up (requires a strashed network)
CutTable Lsv_NtkEnumCuts(Abc_Ntk_t *pNtk, int k);

// Truth table of pRoot as a function of the cut leaves (bit-parallel simulation)
uint64_t Lsv_CutTt(Abc_Obj_t *pRoot, const Cut &cut);

// lsv_cut_tt: print every cut of every AND node with its truth table
void Lsv_NtkPrintCutTt(Abc_Ntk_t *pNtk, int k);

// ===================== PA1 4.2: cut BDD size =====================

// Build the ROBDD of pRoot over the cut leaves and return its size (Cudd_DagSize)
// Variable order: the j-th leaf (ascending ID) is BDD variable j, so smaller IDs are closer to the root
int Lsv_CutBddSize(DdManager *dd, Abc_Obj_t *pRoot, const Cut &cut);

// lsv_cut_bddsize: print every cut of every AND node with its BDD size
void Lsv_NtkPrintCutBddSize(Abc_Ntk_t *pNtk, int k);

#endif
