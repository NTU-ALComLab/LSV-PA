#include "lsvCut.h"
#include "bdd/cudd/cuddInt.h" // defines ptrint, which Cudd_Not / Cudd_NotCond rely on

#include <algorithm>
#include <cassert>
#include <iostream>
#include <iterator>
#include <set>

// A cut with a single leaf (used for PIs and trivial cuts)
static Cut Lsv_CutSingle(int id)
{
  Cut c;
  c.leaves.push_back(id);
  c.sign = (uint64_t)1 << (id % 64);
  return c;
}

// Union of two sorted cuts (sorted, no duplicates)
// The result is written to u, so the caller can reuse one buffer instead of allocating a new vector per merge
void Lsv_CutMerge(const Cut &a, const Cut &b, Cut &u)
{
  u.leaves.clear();
  std::set_union(a.leaves.begin(), a.leaves.end(), b.leaves.begin(), b.leaves.end(),
                 std::back_inserter(u.leaves));
  u.sign = a.sign | b.sign; // signature of a union = OR of the two signatures
}

// Enumerate all k-feasible cuts of every node bottom-up
// In a strashed network every fanin is created before its fanout, so it has a smaller ID
CutTable Lsv_NtkEnumCuts(Abc_Ntk_t *pNtk, int k)
{
  CutTable cuts; // cuts[ID] = all cuts of that node
  Abc_Obj_t *pObj;
  int i;

  // PIs: only the trivial cut
  // Abc_NtkForEachPi is a macro (abc.h:516) that expands to
  //   for (i = 0; i < Abc_NtkPiNum(pNtk) && (pObj = Abc_NtkPi(pNtk, i), 1); i++)
  // so the block below is the loop body, with pObj pointing to one PI per iteration
  Abc_NtkForEachPi(pNtk, pObj, i)
  {
    cuts[Abc_ObjId(pObj)].push_back(Lsv_CutSingle(Abc_ObjId(pObj))); // the PI itself
  }

  // AND nodes in ascending ID order, so both fanins are already done
  // Abc_NtkForEachNode is a macro (abc.h:464) that expands to
  //   for (i = 0; i < #objects && (pObj = Abc_NtkObj(pNtk, i), 1); i++)
  //     if (pObj == NULL || !Abc_ObjIsNode(pObj)) {} else { ...loop body... }
  // i.e. it scans all objects by ID and skips everything that is not an AND node (PIs, POs, constant)
  Abc_NtkForEachNode(pNtk, pObj, i)
  {
    int id = Abc_ObjId(pObj);                 // parent node id
    int id0 = Abc_ObjId(Abc_ObjFanin0(pObj)); // fanin0 node id (left child)
    int id1 = Abc_ObjId(Abc_ObjFanin1(pObj)); // fanin1 node id (right child)
    assert(id0 < id && id1 < id);             // fanins are processed first (guaranteed after strash)
    std::vector<Cut> &my = cuts[id];

    my.push_back(Lsv_CutSingle(id)); // trivial cut: the node itself
    std::set<Cut> seen;              // cuts already found for this node, for the duplicate check

    Cut u; // merge buffer, reused across iterations
    for (const Cut &c0 : cuts[id0])
    {
      for (const Cut &c1 : cuts[id1])
      {
        // Signature filter: if the OR of the two signatures has more than k bits set,
        // the union has more than k leaves, so skip the merge entirely.
        // Different IDs may share a bit, which can only undercount, so no valid cut is ever rejected.
        if (__builtin_popcountll(c0.sign | c1.sign) > k)
          continue;
        Lsv_CutMerge(c0, c1, u);
        if ((int)u.leaves.size() > k)
          continue; // too many leaves
        if (!seen.insert(u).second)
          continue; // duplicate (insert fails if the cut is already present)
        my.push_back(u);
      }
    }
  }
  return cuts;
}

// Bit-parallel simulation: returns the whole truth table of pObj over the cut (bit i = row i)
// leafTt[ID] = the input pattern of each cut leaf (e.g. 11110000); recursion stops at leaves
// Internal helper, so static and not declared in the header
static uint64_t Lsv_NodeTt(Abc_Obj_t *pObj, std::map<int, uint64_t> &leafTt)
{
  auto it = leafTt.find(Abc_ObjId(pObj));
  if (it != leafTt.end())
    return it->second; // a leaf: return its pattern

  assert(Abc_AigNodeIsAnd(pObj));                        // the cut blocks every path to the PIs, so this must be an AND
  uint64_t t0 = Lsv_NodeTt(Abc_ObjFanin0(pObj), leafTt); // fanin 0
  uint64_t t1 = Lsv_NodeTt(Abc_ObjFanin1(pObj), leafTt); // fanin 1
  if (Abc_ObjFaninC0(pObj))
    t0 = ~t0; // complemented edge
  if (Abc_ObjFaninC1(pObj))
    t1 = ~t1;
  return t0 & t1; // a bitwise AND evaluates all rows at once
}

// Truth table of pRoot as a function of the cut leaves
uint64_t Lsv_CutTt(Abc_Obj_t *pRoot, const Cut &cut)
{
  int m = cut.leaves.size(); // number of leaves
  int nRows = 1 << m;        // 2^m rows
  std::map<int, uint64_t> leafTt;

  // Step 1: input pattern of each leaf (its column of the truth table)
  // In row idx, the j-th leaf takes bit (m-1-j) of idx, i.e. the smallest ID is the MSB
  for (int j = 0; j < m; j++)
  {
    uint64_t pat = 0;
    for (int idx = 0; idx < nRows; idx++)
      if ((idx >> (m - 1 - j)) & 1) // leaf j is 1 in this row
        pat |= (uint64_t)1 << idx;  // set bit idx
    leafTt[cut.leaves[j]] = pat;
  }

  // Step 2: simulate from the root down to the leaves
  uint64_t tt = Lsv_NodeTt(pRoot, leafTt);

  // Step 3: keep only the low 2^m bits (~ sets the unused high bits)
  // For m = 6 all 64 bits are used, and 1 << 64 would be undefined behavior
  uint64_t mask = (nRows == 64) ? ~(uint64_t)0 : (((uint64_t)1 << nRows) - 1);
  return tt & mask;
}

// lsv_cut_tt: print every cut of every AND node with its truth table
void Lsv_NtkPrintCutTt(Abc_Ntk_t *pNtk, int k)
{
  CutTable cuts = Lsv_NtkEnumCuts(pNtk, k);
  Abc_Obj_t *pObj;
  int i;

  Abc_NtkForEachNode(pNtk, pObj, i)
  {
    int id = Abc_ObjId(pObj);
    for (const Cut &c : cuts[id])
    {
      std::cout << id << ":";
      for (const int &x : c.leaves)
        std::cout << " " << x;
      // uppercase hex (e.g. 2A); switch back to decimal for the node IDs on the next line
      std::cout << ": " << std::hex << std::uppercase << Lsv_CutTt(pObj, c)
                << std::dec << "\n"; // "\n" instead of endl: endl flushes every line, which is slow for millions of lines
    }
  }
  std::cout << std::flush; // flush once so the output stays in order with ABC's printf output
}

// ===================== PA1 4.2: cut BDD size =====================

// Same recursion as Lsv_NodeTt, with BDDs instead of uint64_t
// memo[ID] = BDD of that AIG node; it starts with the cut leaves, so the recursion stops there
// Computed nodes are memoized as well, so a node reached twice is built only once
// Every BDD in memo is referenced (Cudd_Ref); the caller dereferences all of them
static DdNode *Lsv_NodeBdd(DdManager *dd, Abc_Obj_t *pObj, std::map<int, DdNode *> &memo)
{
  auto it = memo.find(Abc_ObjId(pObj));
  if (it != memo.end())
    return it->second; // a leaf or already computed

  assert(Abc_AigNodeIsAnd(pObj));                          // the cut blocks every path to the PIs, so this must be an AND
  DdNode *f0 = Lsv_NodeBdd(dd, Abc_ObjFanin0(pObj), memo); // fanin 0
  DdNode *f1 = Lsv_NodeBdd(dd, Abc_ObjFanin1(pObj), memo); // fanin 1
  f0 = Cudd_NotCond(f0, Abc_ObjFaninC0(pObj));             // complemented edge: flips a pointer bit, no new node
  f1 = Cudd_NotCond(f1, Abc_ObjFaninC1(pObj));

  DdNode *f = Cudd_bddAnd(dd, f0, f1); // AND = ite(f0, f1, 0); CUDD keeps the result reduced
  Cudd_Ref(f);                         // keep it alive until the caller dereferences it
  memo[Abc_ObjId(pObj)] = f;
  return f;
}

// Build the ROBDD of pRoot over the cut leaves and return its size
int Lsv_CutBddSize(DdManager *dd, Abc_Obj_t *pRoot, const Cut &cut)
{
  std::map<int, DdNode *> memo;

  // Step 1: the j-th leaf becomes BDD variable j
  // Reordering is off, so variable j stays at level j: smaller IDs are closer to the root
  for (int j = 0; j < (int)cut.leaves.size(); j++)
  {
    DdNode *v = Cudd_bddIthVar(dd, j);
    Cudd_Ref(v); // referenced like every other entry, so all of memo can be dereferenced uniformly
    memo[cut.leaves[j]] = v;
  }

  // Step 2: build the BDD from the root down to the leaves
  DdNode *f = Lsv_NodeBdd(dd, pRoot, memo);

  // Step 3: count nodes (internal nodes + 1 terminal)
  int size = Cudd_DagSize(f);

  // Step 4: release every BDD built for this cut
  for (auto &p : memo)
    Cudd_RecursiveDeref(dd, p.second);
  return size;
}

// lsv_cut_bddsize: print every cut of every AND node with its BDD size
void Lsv_NtkPrintCutBddSize(Abc_Ntk_t *pNtk, int k)
{
  CutTable cuts = Lsv_NtkEnumCuts(pNtk, k);
  // One BDD manager for the whole command; each cut dereferences its BDDs when done
  DdManager *dd = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Abc_Obj_t *pObj;
  int i;

  Abc_NtkForEachNode(pNtk, pObj, i)
  {
    int id = Abc_ObjId(pObj);
    for (const Cut &c : cuts[id])
    {
      std::cout << id << ":";
      for (const int &x : c.leaves)
        std::cout << " " << x;
      std::cout << ": " << Lsv_CutBddSize(dd, pObj, c) << "\n";
    }
  }
  std::cout << std::flush;

  assert(Cudd_CheckZeroRef(dd) == 0); // every Cudd_Ref has a matching deref (no leaked nodes)
  Cudd_Quit(dd);
}
