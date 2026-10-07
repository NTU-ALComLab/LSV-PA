# LSV PA1 — Exercise 4: k-feasible Cuts

R15921090 Tse-Chuan Yang

## Files

| File | Contents |
|---|---|
| `lsvCmd.cpp` | Registers the ABC commands (`init`) and implements their entry points: argument parsing and checking that the network has been strashed |
| `lsvCut.h` | The `Cut` and `CutTable` types and declarations of the cut functions |
| `lsvCut.cpp` | Cut enumeration, truth tables (4.1), BDD sizes (4.2), and output |
| `module.make` | Adds `lsvCmd.cpp` and `lsvCut.cpp` to the ABC build |

## Build and Run

```bash
make -j8
./abc
```

```
abc 01> read lsv/pa1/example.blif
abc 02> strash
abc 03> lsv_cut_tt 3
abc 04> lsv_cut_bddsize 3
```

## Commands

### `lsv_cut_tt <k>` (4.1)

Enumerates all k-feasible cuts of every AND node and prints the truth table of each cut in hexadecimal.

```
<node>: <cut leaves in ascending order>: <truth table>
```

Example (Fig. 1 of the assignment, `lsv/pa1/example.blif`):

```
5: 5: 2
5: 1 2: 4
6: 6: 2
6: 2 3: 8
7: 7: 2
7: 5 6: 4
7: 2 3 5: 2A
7: 1 2 6: 10
7: 1 2 3: 30
```

### `lsv_cut_bddsize <k>` (4.2)

Enumerates all k-feasible cuts of every AND node and prints the size of each cut's ROBDD
(`Cudd_DagSize`). Variables are ordered by node ID, with smaller IDs closer to the root.

```
<node>: <cut leaves in ascending order>: <BDD size>
```

Example (Fig. 1):

```
5: 5: 2
5: 1 2: 3
6: 6: 2
6: 2 3: 3
7: 7: 2
7: 5 6: 3
7: 2 3 5: 4
7: 1 2 6: 4
7: 1 2 3: 3
```

## Algorithms

### Cut enumeration — `Lsv_NtkEnumCuts`

Cuts are computed bottom-up and stored in `CutTable cuts` (`cuts[ID]` = all cuts of that node):

1. A PI has only its trivial cut `{itself}`.
2. AND nodes n (with fanins n0, n1) are processed in ascending ID order:
   - add the trivial cut `{n}`;
   - take the union (`Lsv_CutMerge`) of every pair in `cuts[n0] × cuts[n1]`;
   - discard unions with more than k leaves and duplicates.

In a strashed AIG every fanin has a smaller ID than its fanout (a new object's ID is the
current object count; see `src/base/abc/abcObj.c`), so the fanins' cuts are always ready when
a node is processed. This is checked by `assert(id0 < id && id1 < id)`.

The leaves of a cut are kept in a sorted `std::vector<int>`. `std::set_union` preserves the
order, so the output already lists the leaves in ascending order.

### Truth table — `Lsv_CutTt`

Bit-parallel simulation: bit idx of a `uint64_t` holds row idx of the truth table, so all
2^m rows (m = cut size ≤ 6) are computed at once.

1. **Leaf patterns**: in row idx, the j-th leaf (ascending ID) takes bit `(m-1-j)` of idx,
   so the smallest ID is the most significant bit of the input assignment.
   For m = 3 the three leaf patterns are `0xF0`, `0xCC`, and `0xAA`.
2. **Recursion** (`Lsv_NodeTt`): starting at the root, a leaf returns its pattern; any other
   node combines its two fanins with `&`, applying `~` on complemented edges.
   The cut blocks every path from the root to the PIs, so the recursion always ends at leaves.
3. **Mask**: `~` sets the bits above 2^m, so the result is ANDed with `(1 << 2^m) - 1`.
   For m = 6 all 64 bits are used, and `1 << 64` would be undefined behavior, so the mask is all ones.

Example: node 7, cut `{2, 3, 5}`

```
n6 = x1 & x2   = 0xF0 & 0xCC  = 0xC0
n7 = n5 & ~n6  = 0xAA & ~0xC0 = 0x2A
```

### BDD size — `Lsv_CutBddSize`

The same recursion as the truth table, with CUDD BDDs instead of `uint64_t`. Only CUDD's basic
operations (`Cudd_bddIthVar`, `Cudd_bddAnd`, `Cudd_NotCond`) are used; none of ABC's built-in
BDD construction functions are called.

1. **Leaves to variables**: the j-th leaf is `Cudd_bddIthVar(dd, j)`. Dynamic reordering is off,
   so variable j stays at level j and the smallest ID is at the top, as the assignment requires.
2. **Recursion** (`Lsv_NodeBdd`): a leaf returns its variable; any other node combines its two
   fanins with `Cudd_bddAnd`, using `Cudd_NotCond` on complemented edges (this only flips a
   pointer bit and creates no node). CUDD keeps the result reduced.
   Computed nodes are memoized in `memo` (AIG node ID → BDD), so each node is built once per cut.
3. **Size**: `Cudd_DagSize`. CUDD uses complemented edges and a single terminal, so the size is
   the number of internal nodes plus one. For example, `7: 1 2 3` reduces to x0·x1',
   so x2 disappears and the size is 3.
4. **Memory**: every BDD in `memo` is referenced once with `Cudd_Ref` and released with
   `Cudd_RecursiveDeref` after the cut is done. One `DdManager` is shared by the whole command;
   before `Cudd_Quit`, `assert(Cudd_CheckZeroRef(dd) == 0)` confirms that no reference leaked.

`Cudd_NotCond` relies on the `ptrint` type defined in `bdd/cudd/cuddInt.h`, so `lsvCut.cpp`
includes that header as well.

## Optimization

To speed up enumeration, each cut also stores a signature next to its leaves:

```cpp
struct Cut
{
  std::vector<int> leaves; // leaf node IDs in ascending order
  uint64_t sign = 0;       // signature
};
```

The number of candidate cuts of a node is the product of its fanins' cut counts. On large
circuits with k = 6 a single node can have tens of thousands of pairs to merge, and **almost
all of them exceed k and are discarded**. The first version allocated a new vector for every
pair, merged it completely, and only then checked the size; log2 took about two hours.
The optimized loop works as follows:

1. **Signature filter**: each leaf sets bit `ID % 64` of the cut's 64-bit signature `sign`, and
   the signature of a union is the OR of the two signatures. Before merging, the loop checks
   `popcount(c0.sign | c1.sign)`; if it exceeds k, the union must have more than k leaves, so
   **the pair is skipped without merging**. Two IDs may map to the same bit, which can only
   lower the count, so a valid cut is never rejected. Most pairs are eliminated here, making
   this by far the most effective change.
2. **Reused merge buffer**: unions are written into a single `Cut u` declared outside the loop
   and cleared before each merge, instead of allocating a new vector each time.
3. **Duplicate check with `std::set`**: instead of comparing against every existing cut with
   `std::find`, duplicates are detected by the return value of `std::set::insert`.

The corresponding loop in `Lsv_NtkEnumCuts`:

```cpp
Cut u; // merge buffer, reused across iterations (2)
for (const Cut &c0 : cuts[id0])
{
  for (const Cut &c1 : cuts[id1])
  {
    if (__builtin_popcountll(c0.sign | c1.sign) > k)
      continue; // too large according to the signature, no merge needed (1)
    Lsv_CutMerge(c0, c1, u);
    if ((int)u.leaves.size() > k)
      continue; // too many leaves
    if (!seen.insert(u).second)
      continue; // duplicate; seen is a std::set<Cut> (3)
    my.push_back(u);
  }
}
```

On log2 with k = 6, `lsv_cut_tt` dropped from about two hours to about 16 seconds.
