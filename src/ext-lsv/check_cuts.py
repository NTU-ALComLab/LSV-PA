#!/usr/bin/env python3
"""Check lsv cut tt / lsv cut bddsize against an independent oracle.

ABC's `cut` command computes k-feasible cuts and truth tables internally, but
it does not print the homework lines and it drops dominated cuts by default.
There is no ABC command that prints a per-cut ROBDD node count. This script
rebuilds the AIG from the AIGER dump (AND nodes and complement bits), simulates
each cut, and counts a complement-edge ROBDD with variable order = node id.
"""

import os
import random
import re
import subprocess
import sys
import tempfile

ABC = os.path.join(os.path.dirname(__file__), "..", "..", "abc")
ABC = os.path.abspath(ABC)

FIG1 = """\
.model fig1
.inputs x0 x1 x2
.outputs y0
.names x0 x1 n5
10 1
.names x1 x2 n6
11 1
.names n5 n6 y0
10 1
.end
"""

# PDF Fig. 1, lsv cut tt 3 / lsv cut bddsize 3.
FIG1_TT = """\
5: 5: 2
5: 1 2: 4
6: 6: 2
6: 2 3: 8
7: 7: 2
7: 5 6: 4
7: 2 3 5: 2A
7: 1 2 6: 10
7: 1 2 3: 30
"""

FIG1_BDD = """\
5: 5: 2
5: 1 2: 3
6: 6: 2
6: 2 3: 3
7: 7: 2
7: 5 6: 3
7: 2 3 5: 4
7: 1 2 6: 4
7: 1 2 3: 3
"""


def run_abc(blif_path, k):
    with tempfile.TemporaryDirectory() as tmp:
        aig_path = os.path.join(tmp, "net.aig")
        cmd = (
            f"read {blif_path}; strash; write_aiger {aig_path}; "
            f"lsv_print_nodes; echo MARK_TT; lsv cut tt {k}; "
            f"echo MARK_BDD; lsv cut bddsize {k}"
        )
        proc = subprocess.run(
            [ABC, "-c", cmd],
            check=False,
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0 or not os.path.exists(aig_path):
            raise SystemExit(
                "abc failed\n"
                + proc.stdout
                + proc.stderr
            )
        with open(aig_path, "rb") as f:
            aig = f.read()
    return proc.stdout, aig


def parse_stdout(text):
    nodes = []
    mode = "nodes"
    tt_lines = []
    bdd_lines = []
    current = None
    for line in text.splitlines():
        if line.startswith("MARK_TT"):
            mode = "tt"
            continue
        if line.startswith("MARK_BDD"):
            mode = "bdd"
            continue
        if mode == "nodes":
            m = re.match(r"Object Id = (\d+), name = (\S+)", line)
            if m:
                current = {
                    "id": int(m.group(1)),
                    "name": m.group(2),
                    "fanins": [],
                }
                nodes.append(current)
                continue
            m = re.match(r"\s+Fanin-(\d+): Id = (\d+), name = (\S+)", line)
            if m and current is not None:
                current["fanins"].append((int(m.group(2)), m.group(3)))
        elif mode == "tt" and re.match(r"\d+:", line):
            tt_lines.append(line.strip())
        elif mode == "bdd" and re.match(r"\d+:", line):
            bdd_lines.append(line.strip())
    return nodes, tt_lines, bdd_lines


def decode_unsigned(data, i):
    value = 0
    shift = 0
    while True:
        ch = data[i]
        i += 1
        value |= (ch & 0x7F) << shift
        if ch & 0x80 == 0:
            return value, i
        shift += 7


def parse_aiger(data):
    newline = data.index(b"\n")
    header = data[:newline].decode().split()
    if header[0] != "aig":
        raise SystemExit(f"expected binary aiger, got {header[0]}")
    m, i_count, l_count, o_count, a_count = map(int, header[1:6])
    rest = data[newline + 1 :]
    # Latch and output literals are ASCII lines. AND deltas follow in binary.
    lines = []
    idx = 0
    for _ in range(l_count + o_count):
        end = rest.index(b"\n", idx)
        lines.append(rest[idx:end].decode())
        idx = end + 1
    binary = rest[idx:]
    pos = 0
    ands = []
    for gate in range(a_count):
        var = i_count + l_count + 1 + gate
        lit = var << 1
        delta1, pos = decode_unsigned(binary, pos)
        delta0, pos = decode_unsigned(binary, pos)
        lit1 = lit - delta1
        lit0 = lit1 - delta0
        ands.append((var, lit0, lit1))
    return {
        "m": m,
        "i": i_count,
        "l": l_count,
        "o": o_count,
        "ands": ands,
    }


def parse_inputs(blif_text):
    logical = []
    pending = ""
    for line in blif_text.splitlines():
        pending = f"{pending} {line}" if pending else line
        if pending.endswith("\\"):
            pending = pending[:-1]
            continue
        logical.append(pending)
        pending = ""
    names = []
    for line in logical:
        stripped = line.strip()
        if stripped.startswith(".inputs"):
            names.extend(stripped.split()[1:])
    if not names:
        raise SystemExit("BLIF has no .inputs")
    return names


def build_gates(blif_text, nodes, aig):
    if aig["l"] != 0:
        raise SystemExit("checker only supports combinational AIGs")
    inputs = parse_inputs(blif_text)
    if len(inputs) != aig["i"]:
        raise SystemExit("PI count mismatch between BLIF and AIGER")
    name_to_id = {}
    for node in nodes:
        name_to_id[node["name"]] = node["id"]
        for fid, fname in node["fanins"]:
            name_to_id.setdefault(fname, fid)

    aiger_to_abc = {0: 0}
    for index, name in enumerate(inputs, start=1):
        # A PI that strash does not connect to any AND has no fanin line.
        if name in name_to_id:
            aiger_to_abc[index] = name_to_id[name]

    and_nodes = sorted(nodes, key=lambda n: n["id"])
    if len(and_nodes) != len(aig["ands"]):
        raise SystemExit(
            f"AND count mismatch: abc {len(and_nodes)} aiger {len(aig['ands'])}"
        )
    for gate_index, node in enumerate(and_nodes):
        aiger_to_abc[aig["i"] + 1 + gate_index] = node["id"]

    gates = {}
    for node, (_, lit0, lit1) in zip(and_nodes, aig["ands"]):
        fans = []
        for lit in (lit0, lit1):
            var = lit >> 1
            compl = lit & 1
            abc_id = aiger_to_abc[var]
            if var == 0:
                # ABC's const-1 is AIGER literal 0. Flip to recover the ABC value.
                compl ^= 1
            fans.append((abc_id, compl))
        fanin_ids = [fid for fid, _ in node["fanins"]]
        got_ids = sorted(fid for fid, _ in fans)
        if sorted(fanin_ids) != got_ids:
            raise SystemExit(
                f"node {node['id']} fanins {fanin_ids} != aiger {got_ids}"
            )
        by_id = {fid: compl for fid, compl in fans}
        # lsv_print_nodes order is fanin0, fanin1. AIGER sorts literals.
        gates[node["id"]] = (
            fanin_ids[0],
            by_id[fanin_ids[0]],
            fanin_ids[1],
            by_id[fanin_ids[1]],
        )
    pi_ids = [name_to_id[name] for name in inputs if name in name_to_id]
    return gates, pi_ids


def enumerate_cuts(gates, pi_ids, k):
    pi_set = set(pi_ids)
    memo = {}

    def cuts_of(nid):
        if nid in memo:
            return memo[nid]
        if nid not in gates or nid in pi_set:
            memo[nid] = [[nid]]
            return memo[nid]
        f0, _, f1, _ = gates[nid]
        result = [[nid]]
        seen = {(nid,)}
        for c0 in cuts_of(f0):
            for c1 in cuts_of(f1):
                leaves = tuple(sorted(set(c0 + c1)))
                if len(leaves) > k or leaves in seen:
                    continue
                seen.add(leaves)
                result.append(list(leaves))
        memo[nid] = result
        return result

    lines = []
    for nid in sorted(gates):
        lines.append((nid, cuts_of(nid)))
    return lines


def eval_gate(gates, nid, assign, memo):
    if nid in assign:
        return assign[nid]
    if nid in memo:
        return memo[nid]
    if nid == 0:
        return 1
    f0, c0, f1, c1 = gates[nid]
    value = (eval_gate(gates, f0, assign, memo) ^ c0) & (
        eval_gate(gates, f1, assign, memo) ^ c1
    )
    memo[nid] = value
    return value


def truth_table(gates, root, leaves):
    n = len(leaves)
    tt = 0
    for i in range(1 << n):
        assign = {}
        for j, leaf in enumerate(leaves):
            assign[leaf] = (i >> (n - 1 - j)) & 1
        if eval_gate(gates, root, assign, {}):
            tt |= 1 << i
    return tt


class Robdd:
    def __init__(self):
        self.nodes = {}
        self.unique = {}
        self.next_id = 2

    def mk(self, var, then, els):
        if then == els:
            return then
        complement = False
        if then < 0:
            then, els = -then, -els
            complement = True
        key = (var, then, els)
        node = self.unique.get(key)
        if node is None:
            node = self.next_id
            self.next_id += 1
            self.unique[key] = node
            self.nodes[node] = key
        return -node if complement else node

    def build(self, var_ids, tt):
        n = len(var_ids)

        def rec(level, sub, width):
            if sub == 0:
                return -1
            if sub == (1 << width) - 1:
                return 1
            half = width // 2
            els = rec(level + 1, sub & ((1 << half) - 1), half)
            then = rec(level + 1, sub >> half, half)
            return self.mk(var_ids[level], then, els)

        return rec(0, tt, 1 << n)

    def dag_size(self, node):
        seen = set()

        def rec(n):
            n = abs(n)
            if n in seen:
                return
            seen.add(n)
            if n == 1:
                return
            _, then, els = self.nodes[n]
            rec(then)
            rec(els)

        rec(node)
        return len(seen)


def format_tt(nid, leaves, tt):
    body = " ".join(str(leaf) for leaf in leaves)
    return f"{nid}: {body}: {tt:X}"


def format_bdd(nid, leaves, size):
    body = " ".join(str(leaf) for leaf in leaves)
    return f"{nid}: {body}: {size}"


def expected_lines(gates, pi_ids, k):
    tt_lines = []
    bdd_lines = []
    bdd = Robdd()
    for nid, cuts in enumerate_cuts(gates, pi_ids, k):
        for leaves in cuts:
            tt = truth_table(gates, nid, leaves)
            tt_lines.append(format_tt(nid, leaves, tt))
            size = bdd.dag_size(bdd.build(leaves, tt))
            bdd_lines.append(format_bdd(nid, leaves, size))
    return tt_lines, bdd_lines


def check_case(name, blif_text, k, exact_tt=None, exact_bdd=None):
    with tempfile.NamedTemporaryFile("w", suffix=".blif", delete=False) as f:
        f.write(blif_text)
        blif_path = f.name
    try:
        stdout, aig_bytes = run_abc(blif_path, k)
    finally:
        os.unlink(blif_path)
    nodes, got_tt, got_bdd = parse_stdout(stdout)
    aig = parse_aiger(aig_bytes)
    if not aig["ands"] and not nodes:
        exp_tt, exp_bdd = [], []
    else:
        gates, pi_ids = build_gates(blif_text, nodes, aig)
        exp_tt, exp_bdd = expected_lines(gates, pi_ids, k)
    ok = True
    if got_tt != exp_tt:
        ok = False
        print(f"FAIL {name} k={k} truth table")
        report_diff(got_tt, exp_tt)
    if got_bdd != exp_bdd:
        ok = False
        print(f"FAIL {name} k={k} bdd size")
        report_diff(got_bdd, exp_bdd)
    if exact_tt is not None and got_tt != exact_tt.strip().splitlines():
        ok = False
        print(f"FAIL {name} k={k} does not match the PDF sample")
    if exact_bdd is not None and got_bdd != exact_bdd.strip().splitlines():
        ok = False
        print(f"FAIL {name} k={k} BDD sample does not match the PDF")
    if ok:
        print(f"PASS {name} k={k}  cuts={len(got_tt)}")
    return ok


def report_diff(got, exp):
    print(f"  counts got={len(got)} expected={len(exp)}")
    limit = max(len(got), len(exp))
    shown = 0
    for i in range(limit):
        g = got[i] if i < len(got) else "<missing>"
        e = exp[i] if i < len(exp) else "<missing>"
        if g != e:
            print(f"  first diffs around {i}:")
            for j in range(max(0, i - 1), min(limit, i + 3)):
                gj = got[j] if j < len(got) else "<missing>"
                ej = exp[j] if j < len(exp) else "<missing>"
                print(f"    [{j}] got {gj}")
                print(f"         exp {ej}")
            shown += 1
            if shown == 2:
                break


def sop(op, a, b, y):
    if op == "and":
        cubes = ["11 1"]
    elif op == "nand":
        cubes = ["0- 1", "-0 1"]
    elif op == "or":
        cubes = ["1- 1", "-1 1"]
    elif op == "xor":
        cubes = ["01 1", "10 1"]
    elif op == "xnor":
        cubes = ["00 1", "11 1"]
    else:
        raise ValueError(op)
    body = "\n".join(cubes)
    return f".names {a} {b} {y}\n{body}\n"


def blif(name, pis, pos, gates):
    return (
        f".model {name}\n"
        f".inputs {' '.join(pis)}\n"
        f".outputs {' '.join(pos)}\n"
        + "".join(gates)
        + ".end\n"
    )


def and_chain(n):
    pis = [f"p{i}" for i in range(n)]
    gates = []
    prev = pis[0]
    for i in range(1, n):
        nxt = f"n{i}"
        gates.append(sop("and", prev, pis[i], nxt))
        prev = nxt
    return blif("chain", pis, [prev], gates)


def xnor_of_ands():
    # The shape that broke child-truth-table composition:
    # p = a&~b, q = ~a&b, y = ~p&~q, while a and b are themselves ANDs.
    gates = [
        sop("and", "a", "b", "u"),
        sop("and", "c", "d", "v"),
        sop("xnor", "u", "v", "y"),
    ]
    return blif("xnor", ["a", "b", "c", "d"], ["y"], gates)


def shared_cone(depth):
    # Two branches share a prefix, then merge. Cuts of the merge can contain
    # both a node and the inputs that node was expanded into.
    pis = ["a", "b", "c"]
    gates = [sop("xor", "a", "b", "s0")]
    prev = "s0"
    for i in range(1, depth):
        nxt = f"s{i}"
        gates.append(sop("xor", prev, "c" if i % 2 == 0 else "a", nxt))
        prev = nxt
    gates.append(sop("and", prev, "s0", "left"))
    gates.append(sop("or", prev, "b", "right"))
    gates.append(sop("xor", "left", "right", "y"))
    return blif("shared", pis, ["y"], gates)


def random_network(rng, n_pi, n_gates, n_po):
    pis = [f"p{i}" for i in range(n_pi)]
    signals = list(pis)
    gates = []
    ops = ["and", "nand", "or", "xor", "xnor"]
    for g in range(n_gates):
        a = rng.choice(signals)
        b = rng.choice(signals)
        name = f"g{g}"
        gates.append(sop(rng.choice(ops), a, b, name))
        signals.append(name)
    pos = signals[-n_po:]
    return blif("rand", pis, pos, gates)


def const_and_buf():
    # Constant 0 is a names record with no fanin and no cubes.
    gates = [
        ".names zero\n",
        ".names one\n1\n",
        sop("and", "zero", "b", "y0"),
        sop("or", "one", "b", "y1"),
        sop("xor", "a", "a", "y2"),
        ".names a y3\n0 1\n",
    ]
    return blif("fold", ["a", "b"], ["y0", "y1", "y2", "y3"], gates)


def run_cmd(command):
    proc = subprocess.run(
        [ABC, "-c", command],
        check=False,
        capture_output=True,
        text=True,
    )
    return proc.stdout + proc.stderr


def parse_cut_lines(text):
    rows = []
    for line in text.splitlines():
        match = re.match(r"^(\d+):((?: \d+)*): ([0-9A-F]+)$", line.strip())
        if match:
            leaves = [int(x) for x in match.group(2).split()]
            rows.append((int(match.group(1)), leaves, match.group(3)))
    return rows


def assert_cut_shape(rows, k):
    previous = -1
    current = None
    first = True
    for node, leaves, _payload in rows:
        if not leaves or len(leaves) > k:
            raise SystemExit(f"bad leaf count {leaves} at node {node}")
        if leaves != sorted(leaves):
            raise SystemExit(f"leaves not sorted at node {node}: {leaves}")
        if node < previous:
            raise SystemExit(f"node ids decreased: {previous} then {node}")
        if node != current:
            if node < previous or (current is not None and node <= current):
                raise SystemExit(f"node order {current} -> {node}")
            if leaves != [node]:
                raise SystemExit(f"node {node} does not start with the trivial cut")
            current = node
            previous = node
            first = False
        elif first:
            raise SystemExit("internal shape error")
    return True


def check_format(name, blif_path, k):
    tt = run_cmd(f"read {blif_path}; strash; lsv cut tt {k}")
    bdd = run_cmd(f"read {blif_path}; strash; lsv cut bddsize {k}")
    if "Empty network" in tt or "not structurally hashed" in tt:
        print(f"FAIL {name} k={k} command error\n{tt}")
        return False
    tt_rows = parse_cut_lines(tt)
    bdd_rows = parse_cut_lines(bdd)
    try:
        assert_cut_shape(tt_rows, k)
        assert_cut_shape(bdd_rows, k)
    except SystemExit as exc:
        print(f"FAIL {name} k={k} {exc}")
        return False
    tt_cuts = [(n, leaves) for n, leaves, _ in tt_rows]
    bdd_cuts = [(n, leaves) for n, leaves, _ in bdd_rows]
    if tt_cuts != bdd_cuts:
        print(f"FAIL {name} k={k} tt/bddsize cut lists differ")
        return False
    if any(int(size) < 1 for _n, _leaves, size in bdd_rows):
        print(f"FAIL {name} k={k} non-positive BDD size")
        return False
    print(f"PASS {name} k={k}  format cuts={len(tt_rows)}")
    return True


def check_messages():
    fig = None
    with tempfile.NamedTemporaryFile("w", suffix=".blif", delete=False) as handle:
        handle.write(FIG1)
        fig = handle.name
    ok = True
    checks = [
        ("empty", "lsv cut tt 3", "Empty network"),
        ("not-strash", f"read {fig}; lsv cut tt 3", "not structurally hashed"),
        ("k-hi", f"read {fig}; strash; lsv cut tt 7", "k must be an integer"),
        ("k-lo", f"read {fig}; strash; lsv cut tt 0", "k must be an integer"),
        ("k-word", f"read {fig}; strash; lsv cut tt foo", "k must be an integer"),
        ("usage", "lsv cut", "usage: lsv cut tt"),
    ]
    try:
        for name, command, needle in checks:
            out = run_cmd(command)
            if needle not in out:
                ok = False
                print(f"FAIL interface {name}\n{out}")
            else:
                print(f"PASS interface {name}")
    finally:
        os.unlink(fig)
    return ok


def check_k1_and_inverter():
    ok = True
    ok &= check_case(
        "fig1-k1",
        FIG1,
        1,
        "5: 5: 2\n6: 6: 2\n7: 7: 2\n",
        "5: 5: 2\n6: 6: 2\n7: 7: 2\n",
    )
    inverter = (
        ".model inv\n.inputs a\n.outputs y\n.names a y\n0 1\n.end\n"
    )
    ok &= check_case("inverter", inverter, 4, "", "")
    return ok


def check_latch():
    text = (
        ".model latch\n.inputs a\n.outputs y\n.latch n lo 0\n"
        ".names a lo n\n11 1\n.names n y\n1 1\n.end\n"
    )
    with tempfile.NamedTemporaryFile("w", suffix=".blif", delete=False) as handle:
        handle.write(text)
        path = handle.name
    try:
        tt = run_cmd(f"read {path}; strash; lsv cut tt 3")
        bdd = run_cmd(f"read {path}; strash; lsv cut bddsize 3")
    finally:
        os.unlink(path)
    tt_rows = parse_cut_lines(tt)
    bdd_rows = parse_cut_lines(bdd)
    expect_tt = [(6, [6], "2"), (6, [1, 5], "8")]
    expect_bdd = [(6, [6], "2"), (6, [1, 5], "3")]
    if tt_rows != expect_tt or bdd_rows != expect_bdd:
        print("FAIL latch")
        print(" tt", tt_rows)
        print(" bdd", bdd_rows)
        return False
    print("PASS latch k=3  cuts=2")
    return True


def main():
    mul_path = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..", "lsv", "pa1", "mul.blif")
    )
    with open(mul_path) as f:
        mul = f.read()
    ok = True
    ok &= check_case("fig1", FIG1, 3, FIG1_TT, FIG1_BDD)
    ok &= check_case("fig1", FIG1, 2)
    ok &= check_case("mul", mul, 3)
    ok &= check_case("mul", mul, 6)
    ok &= check_case("xnor-of-ands", xnor_of_ands(), 6)
    ok &= check_case("and-chain-12", and_chain(12), 6)
    ok &= check_case("shared-8", shared_cone(8), 6)
    ok &= check_case("const-fold", const_and_buf(), 4)
    rng = random.Random(20261009)
    for seed_i in range(12):
        net = random_network(rng, n_pi=5, n_gates=16, n_po=3)
        for k in (2, 4, 6):
            ok &= check_case(f"rand{seed_i}", net, k)
    ok &= check_messages()
    ok &= check_k1_and_inverter()
    ok &= check_latch()
    bench = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..", "lsv", "pa1", "benchmarks")
    )
    for name, ks in (
        ("int2float", (2, 6)),
        ("adder", (2, 6)),
        ("router", (2, 6)),
        ("mem_ctrl", (6,)),
    ):
        with open(os.path.join(bench, name + ".blif")) as handle:
            text = handle.read()
        for k in ks:
            ok &= check_case(name, text, k)
    for name in ("div", "log2", "sqrt", "square"):
        ok &= check_format(name, os.path.join(bench, name + ".blif"), 2)
    if not ok:
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
