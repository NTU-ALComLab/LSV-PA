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

### Precomputed regions and exact cut size

Each PA1 option stores its leaves and the ANDs reached from its root before any leaf.
The root is part of this region. Combining options uses the union of their leaves
and the union of their regions. An AND shared by two options contributes once to
the size. We reject combinations where either region contains a leaf of the other,
because the full cut must stop at that leaf.

This compatibility check preserves every legal cut. For each root of a legal
cut, take the first leaves reached along its fanin paths. K3 gives each such leaf
a path to a PI that avoids the other leaves, so the first-hit set is a minimal
PA1 cut of that root. Those local regions all avoid the full leaf set and their
union reconstructs the cut. On a compatible branch every leaf is already reachable
from a root. The remaining K3 check depends only on the leaf set, so its result is
cached across candidates.

### Boundary roots and pruning

The search tries roots in decreasing ID order. While adding and removing ANDs it
maintains the number of fanout edges leaving the region. An AND with an outgoing
edge is a required root. An AND with no fanouts is also a required root, so a
dangling region can be reconstructed from the selected roots. A selected root
that loses its last exit can never recover it on that branch as the region grows.

The decreasing order bounds the next root from below. Let x be an exit of the
current region that is not a root yet. In the final cut, x is either a root, or
each of its outside fanouts t is absorbed by a later root r whose cone contains t,
so r ≥ t > x. Either way some later root is at least x, and the next root is the
largest later one. The next root must therefore be at least the largest pending
exit: if that exit is above the root just added, the branch is dead, and otherwise
the root loops stop as soon as they reach smaller IDs. Only when the region is
closed (every exit is a root) may the next root be any smaller AND.

The search records a base cut when the selected roots equal the region's required
roots and the leaves pass K3. Once the maximum size is known, every subset of
interior nodes that fits the root limit is promoted to roots as well. Each of
these promotions keeps the same region and leaves, so the size and K2–K4 still hold.

The subtree bound adds the largest remaining option regions to the current size.
This is an upper bound even if the added regions overlap. Branches below the
maximum can be skipped. Option regions are sorted by size to skip the rest of a
loop once the bound is too small. When U already has k leaves, any option must
be a subset of U. The options are indexed by their smallest leaf, followed by an
exact subset check, so the search can avoid scanning all roots in that case.

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

Times in seconds on the same machine. "First version" is the straightforward
implementation; "Current" is the region-based search with roots in decreasing ID order.

| Case (k l) | First version | Current |
|---|---|---|
| int2float 6 4 | 102.1 | 1.22 |
| int2float 6 3 | 10.9 | 0.14 |
| i10 4 2 | 6.8 | 0.11 |
| router 6 3 | 11.8 | 0.18 |
| adder 6 3 | 4.4 | 0.30 |
| adder 6 4 | 38.2 | 1.17 |
| ctrl 6 3 | 20.2 | 0.34 |
| ctrl 4 4 | 3.5 | 0.12 |
| i10 6 2 | > 60 | 3.17 |
| ctrl 6 4 | > 120 | 6.40 |

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
