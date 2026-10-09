# PA1 Q4: Cut Truth Tables and BDD Sizes

## Build and Run

Build and start ABC from the repository root on Linux or WSL:

```sh
make -j2
./abc
```

At the ABC prompt, run:

```text
read lsv/pa1/example.blif
strash
lsv_cut_tt 3
lsv_cut_bddsize 3
```

The assignment uses `k=2..6`; both commands also accept `k=1`.
Read a network and run `strash` first. Both commands read the current AIG
without modifying it. The original `lsv_print_nodes` command remains available.

## Output and Implementation

Each line has the format `root: leaf IDs: value`, with leaf IDs in increasing order.
`lsv_cut_tt` prints uppercase hexadecimal without a `0x` prefix;
`lsv_cut_bddsize` prints decimal sizes. Only internal AND nodes are printed,
including nodes that do not reach a primary output.

- Each combinational input has a singleton cut; constant 1 has an empty cut.
  Every internal node keeps `{root}` and merges every pair of fanin cuts.
- Sorted union rejects cuts exceeding `k` and duplicate leaf sets. There is no
  dominance pruning, function-based deduplication, or cut-count limit.
  Output follows the order in which cuts are first generated.
- An explicit postorder stack completes fanins first, without assuming contiguous
  or topologically ordered IDs or using deep C++ recursion.
- A cut with `n` leaves uses `2^n` truth-table bits. The smallest leaf ID is the
  most significant input bit, and assignment 0 maps to output bit 0.
  Six inputs use all 64 bits. Simulation stops at every cut leaf and inverts
  only active bits on complemented edges.
- BDD construction uses custom Shannon expansion: the low table half is `x=0`
  and the high half is `x=1`. Variables follow increasing leaf IDs, with dynamic
  reordering disabled. `Cudd_DagSize` includes one physical terminal node,
  so a single-variable function has size 2.
- Cut storage and algorithms are implemented in `lsvCut.cpp`. The implementation
  uses general ABC graph and command APIs and general CUDD operations.
  Builds without CUDD still support `lsv_cut_tt`.

For `example.blif`, `lsv_cut_tt 3` prints:

```text
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

The BDD sizes for the same cuts are `2, 3, 2, 3, 2, 3, 4, 4, 3`, in that order.

## Source Files

| File | Purpose |
| --- | --- |
| `lsvCmd.cpp` | Register LSV commands and preserve node inspection. |
| `lsvCut.h` | Declare the two Q4 command callbacks. |
| `lsvCut.cpp` | Enumerate cuts, compute truth tables, construct BDDs, and print results. |
| `module.make` | Include the implementation in the ABC build. |

## Large Outputs

Redirect output to files when enumerating large networks:

```sh
./abc -c "read lsv/pa1/benchmarks/adder.blif; strash; lsv_cut_tt 6" > adder_tt.txt
./abc -c "read lsv/pa1/benchmarks/adder.blif; strash; lsv_cut_bddsize 6" > adder_bddsize.txt
```
