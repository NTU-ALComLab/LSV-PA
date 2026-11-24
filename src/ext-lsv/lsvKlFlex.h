#ifndef LSV_KL_FLEX_H
#define LSV_KL_FLEX_H

#include "base/abc/abc.h"

#include <iostream>
#include <optional>
#include <string>
#include <vector>

// The two boundaries of a KL cut. All IDs refer to the original AIG and are sorted ascending;
// when leaf or root values are packed into an integer, the smallest ID is the most significant bit.
struct KlCut
{
  std::vector<int> roots;  // V: the signals this sub-circuit provides to the rest of the network
  std::vector<int> leaves; // U: the input boundary where the walk from the roots stops
};

// Phase 1: finds every KL cut of maximum size in the strashed combinational network pNtk.
// k and l bound the numbers of leaves and roots; the size is the number of roots plus interior
// AND nodes. Returns an empty vector if there is no KL cut.
std::vector<KlCut> Lsv_FindMaximumKlCuts(Abc_Ntk_t *pNtk, int k, int l);

// Phase 2: for a KL cut of pNtk, computes the root patterns allowed for every leaf value u.
// Entry u of the result is an uppercase hexadecimal mask; bit c is 1 iff forcing the roots to
// pattern c is allowed. Returns std::nullopt if the AIG/CNF conversion or a SAT call fails.
std::optional<std::vector<std::string>> Lsv_ComputeFlexMasks(Abc_Ntk_t *pNtk, const KlCut &cut);

#endif // LSV_KL_FLEX_H
