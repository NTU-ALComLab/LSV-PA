# LSV PA2 — KL Cut Flexibility Computation

R15921090 Tse-Chuan Yang

## Files

| File | Contents |
|---|---|
| `lsvCmd.cpp` | Registers the ABC commands and implements their entry points: argument parsing, network checks, and printing |
| `lsvKlFlex.h` | The `KlCut` type and the two phase functions used by `lsv_kl_flex` |
| `lsvKlCut.cpp` | Phase 1: enumerates KL cuts, checks (K1)–(K4), and keeps every cut of maximum size |
| `lsvKlFlex.cpp` | Phase 2: computes the flexibility masks of a KL cut with simulation and SAT |
| `lsvCut.h`, `lsvCut.cpp` | PA1: k-feasible cut enumeration and truth tables, reused by PA2 |
| `module.make` | Adds the four source files to the ABC build |

## Build and Run

```bash
make -j8
./abc
```

Fig. 1 of the assignment (z = ac + bc) as BLIF:

```
.model pa2_fig1
.inputs a b c
.outputs z
.names a c v5
11 1
.names b c v6
11 1
.names v5 v6 z
1- 1
-1 1
.end
```

```
abc 01> read fig1.blif
abc 02> strash
abc 03> lsv_kl_flex 3 2
5 7: 1 2 3: A A A 5 A 5 A 5
6 7: 1 2 3: A A A 5 A 5 A 5
7: 1 2 3: 2 2 2 1 2 1 2 1
```

## Command

### `lsv_kl_flex <k> <l>`

Finds every KL cut (U, V) with |U| ≤ k and |V| ≤ l whose size |V| + |I(U, V)| is maximum, and
prints one line per such cut:

```
<v_1> ... <v_m>: <u_1> ... <u_n>: <F_0> <F_1> ... <F_{2^n-1}>
```

- V and U are listed in ascending ID order.
- Leaf value u and root value c are numbered with the smallest ID as the most significant bit.
- `F_u` is the uppercase hexadecimal mask of A(u): bit c is 1 iff c is allowed when the leaves show u.
- If the network has no KL cut, nothing is printed.

The command requires a strashed combinational network. `k` and `l` must be non-negative integers
(trailing characters such as `3x` are rejected). All lines are computed first and printed together,
so a failure never leaves partial output.

## Phase 1: Maximum KL Cuts (`lsvKlCut.cpp`)

### Enumeration

As suggested in the assignment, the leaves that a root reaches without passing another leaf form a
k-feasible cut of that root, and U is the union of these cuts. `Lsv_FindMaximumKlCuts` therefore

1. enumerates the PA1 cuts of every node (`Lsv_NtkEnumCuts`), and
2. picks roots one at a time in ascending ID order (`EnumerateKlCuts`, a recursion up to depth l).
   For every new root, each leaf set U of the previous level is merged with each PA1 cut of the
   root. A merge is kept if it has at most k leaves (signature test first, then the exact union)
   and contains no selected root (K1). Equal leaf sets of the same root set are kept once.

Picking roots only in ascending order generates each root set once. Leaf sets that fail a check are
still passed to the next level, because adding a root may repair a (K4) violation.

Dominated PA1 cuts are omitted, which loses no KL cut: if the leaves reached by a root r strictly
contained another cut C of r, take a leaf x outside C. By (K3), x has a path to a PI that avoids
the other leaves; appended to the path from r to x, it gives a path from r to a PI that avoids C,
contradicting that C is a cut of r.

### Checking (K2)–(K4)

`GetKlCutSize` validates a candidate in four steps and returns |V| + |I|, or -1 if a check fails:

| Step | Function | Check |
|---|---|---|
| 1 | `WalkCutBoundary` | (K2): a DFS from V along fanins that stops at U must not reach a PI. The visited nodes other than roots and leaves form the interior I. Roots may lie in each other's fanin cone, so the walk passes through roots. |
| 2 | `AllLeavesReached` | (K3), part 1: every leaf must have been visited by step 1. |
| 3 | `IsFanoutFree` | (K4): every fanout of an interior node must be visited by step 1 and not be a leaf. POs are never visited, so an interior node driving a PO fails. |
| 4 | `AllLeavesNecessary` | (K3), part 2: removing any AND leaf and walking again must reach a PI. A reached PI leaf is always necessary. |

Steps 2 and 3 read the traversal marks left by step 1 (`Abc_NodeIsTravIdCurrent`), so step 4, which
walks again, runs last.

### Pruning

Only maximum cuts are printed, so a candidate whose size cannot reach the current maximum is skipped.
All pruning below is exact: the output is the same as without it.

1. **Cone upper bound.** cone(r, C) is the number of AND nodes between root r and its PA1 cut C.
   Every interior node is reached from some root r along a path that avoids U, and therefore avoids
   C_r ⊆ U, so |I| ≤ Σ cone(r, C_r). Each leaf set carries the smallest such sum over the cut
   combinations that produced it, and a candidate with |V| + Σ cone below the current maximum is not
   validated. The comparison is strict, because tied cuts must be printed.
2. **Starting maximum.** Before the search, every single-root cut is validated. Since |V| = 1 ≤ l,
   the maximum is at least this value, so pruning works from the start.
3. **Minimal leaf sets.** Every leaf set is a union of cuts of its roots, so it is itself a cut. If
   U1 ⊊ U2 for the same root set, every cut grown from U2 is either equal to one grown from U1 or
   has a redundant leaf (K3). `KeepMinimalUnions` therefore drops non-minimal leaf sets before
   recursing.
4. **Subtree bound.** Adding a root r can raise the bound by at most 1 + (largest cone of r).
   `futureGain` stores, for every position in the root order, the sum of the t largest such values
   among the remaining roots. If |V| + Σ cone + futureGain is below the current maximum, the merge is
   skipped together with everything that would grow from it. On the last level futureGain is 0.
   Leaf sets are sorted by decreasing cone sum and root cuts by decreasing cone, so the bound only
   decreases along both loops and they can `break` at the first failure; a root whose best bound
   is too small is skipped entirely.

## Phase 2: Flexibility (`lsvKlFlex.cpp`)

For every u ∈ B^n the masks follow Step 2 of the assignment: A(u) = B^m if no PI assignment produces
U = u; otherwise c ∈ A(u) iff no PI assignment with U = u changes a PO when the roots are forced to c.
The miter (`BuildKlMiter`) is the one in Fig. 2: two copies sharing the PIs, the roots of the second
copy replaced by new PIs p, the XORs of the PO pairs ORed into `diff`, and the leaves of the original
copy exposed as outputs. The questions differ only in the values of U, p and `diff`, so they are asked
as assumptions to a solver that is built once per cut.

Most questions are answered without SAT. Every shortcut only decides answers that are certain, so
the masks are exactly those of the plain SAT procedure.

1. **Original root value.** When the leaves show u, the roots compute a fixed value f(u) (by K2 they
   are functions of the leaves). Forcing them to f(u) changes nothing, so f(u) is always allowed.
   `OriginalRootValues` computes f(u) from the PA1 truth tables. Its SAT query is always UNSAT but has
   to prove two copies of the circuit equivalent, which takes minutes on large arithmetic circuits.
2. **Simulation.** `SimulateFlex` simulates 2048 pseudo-random inputs (fixed seed, 64 per machine word),
   then, for every c, sets the roots to c and resimulates the nodes after the first root (AND IDs are
   topological, so earlier nodes cannot change). Seeing U = u proves that u occurs, and
   an output change proves that c is not allowed. Only what simulation does not prove goes to SAT.
3. **Solvers on demand.** The question "does U = u occur?" depends only on the logic above the leaves,
   so it uses a small network of the leaves' fanin cone (`BuildLeafCone`, CNF by `Cnf_DeriveSimple`).
   The full miter is built only if some forcing question is left after simulation, and uses the more
   compact `Cnf_Derive` because those questions are the hard ones.

## Verification

- The local regression tests (Fig. 1 and five hand-made circuits covering redundant leaves, external
  fanouts, POs driven by interior nodes, leaves depending on roots, constants and empty output) pass.
- An independent brute-force checker written in Python from the definitions enumerates every (U, V),
  checks (K1)–(K4), and computes A(u) by simulating all PI assignments. It reproduces the table of all
  eleven KL cuts of Fig. 1, and agrees with `lsv_kl_flex` on 9 270 (circuit, k, l) cases from 1 854
  random circuits and on 72 cases from the small example circuits.
- The output is identical to the first, straightforward implementation on 165 cases of the PA1
  benchmarks (ctrl, int2float, router, adder, i10, square, div, log2 and smaller circuits).
- AddressSanitizer and UndefinedBehaviorSanitizer report nothing on 21 test and benchmark cases.

## Performance

Times in seconds, compared with the first, straightforward implementation:

| Case (k l) | First version | Final |
|---|---|---|
| int2float 6 4 | 102.1 | 0.74 |
| int2float 6 3 | 10.9 | 0.11 |
| i10 4 2 | 6.8 | 0.20 |
| router 6 3 | 11.8 | 0.79 |
| adder 6 3 | 4.4 | 0.63 |
| adder 6 4 | 38.2 | 8.2 |
| ctrl 6 3 | 20.2 | 3.3 |
| ctrl 4 4 | 3.5 | 2.2 |
| i10 6 2 | > 60 | 5.7 |
| ctrl 6 4 | > 120 | 110 |

**Limitation.** On large arithmetic circuits such as sqrt, or div with l ≥ 2, some forcing questions
are hard for SAT (one took 900 s) and simulation rarely finds their counterexamples, so these cases
can exceed the 10-minute limit.

## PA1 Commands

The PA1 commands are still available:

- `lsv_cut_tt <k>`: prints every k-feasible cut of every AND node (dominated cuts omitted) with its
  truth table in hexadecimal, as `<node>: <leaves>: <truth table>`.
- `lsv_cut_bddsize <k>`: prints the ROBDD size (`Cudd_DagSize`) of every cut, with variables ordered
  by node ID and smaller IDs closer to the root, as `<node>: <leaves>: <BDD size>`.

Cuts are enumerated bottom-up in ascending ID order: a node's cuts are its trivial cut plus the unions
of its fanins' cuts with at most k leaves, without duplicates and dominated cuts. Each cut stores a
64-bit signature (bit `ID % 64` per leaf), so a pair whose OR has more than k bits is rejected without
merging. Truth tables are computed by bit-parallel simulation, with the smallest leaf ID as the most
significant input bit.
