#!/usr/bin/env python3
"""Run with: python3 src/ext-lsv/tests/test_cut.py [path/to/abc]."""
import itertools
import pathlib
import re
import subprocess
import sys
import tempfile

ABC = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else './abc').resolve()
REPO = pathlib.Path(__file__).resolve().parents[3]


def run(commands):
    result = subprocess.run([str(ABC), '-c', commands], text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return result.stdout


def rows(output, base):
    result = {}
    for root, leaves, value in re.findall(r'^(\d+):([\d ]*): ([0-9A-F]+)$', output, re.M):
        key = int(root), tuple(map(int, leaves.split()))
        assert key not in result, ('duplicate cut', key)
        result[key] = int(value, base)
    return result


def bdd_size(bits):
    # Independent reduced ordered BDD oracle with complemented edges.
    unique = {}
    def build(table):
        if len(set(table)) == 1:
            return 1 if table[0] else -1
        half = len(table) // 2
        low, high = build(table[:half]), build(table[half:])
        if low == high:
            return low
        sign = 1 if high > 0 else -1
        key = len(table), low * sign, high * sign
        if key not in unique:
            unique[key] = len(unique) + 2
        return sign * unique[key]
    build(bits)
    return len(unique) + 1


example = REPO / 'lsv/pa1/example.blif'
prefix = f'read {example}; strash; '
expected = {(5, (5,)): 2, (5, (1, 2)): 4, (6, (6,)): 2,
            (6, (2, 3)): 8, (7, (7,)): 2, (7, (5, 6)): 4,
            (7, (2, 3, 5)): 0x2A, (7, (1, 2, 6)): 0x10,
            (7, (1, 2, 3)): 0x30}
assert rows(run(prefix + 'lsv_cut_tt 3'), 16) == expected
assert rows(run(prefix + 'lsv_cut_bddsize 3'), 10) == {
    key: bdd_size([(truth >> a) & 1 for a in range(1 << len(key[1]))])
    for key, truth in expected.items()}

with tempfile.TemporaryDirectory(prefix='lsv-cut-') as tmp:
    circuit = pathlib.Path(tmp) / 'check.blif'
    # Reconvergence, redundant leaves, and a six-input function. Keep all
    # gates observable so that strash cannot remove an unreferenced gate.
    gates = [('x0', 'x1', 'a'), ('x2', 'x3', 'b'), ('a', 'b', 'c'),
             ('a', 'c', 'd'), ('x4', 'x5', 'e'), ('d', 'e', 'f')]
    circuit.write_text('.model check\n.inputs x0 x1 x2 x3 x4 x5\n.outputs '
                       + ' '.join(g[2] for g in gates) + '\n'
                       + ''.join(f'.names {a} {b} {c}\n11 1\n' for a, b, c in gates)
                       + '.end\n')
    prefix = f'read {circuit}; strash; '
    graph = {}
    current = None
    for line in run(prefix + 'lsv_print_nodes').splitlines():
        match = re.match(r'Object Id = (\d+)', line)
        if match:
            current = int(match[1])
            graph[current] = []
        match = re.match(r'  Fanin-\d+: Id = (\d+)', line)
        if match:
            graph[current].append(int(match[1]))

    # Enumerate by expanding frontiers, independently of fanin-cut merging.
    all_cuts = {}
    for root in graph:
        seen = {frozenset([root])}
        pending = list(seen)
        while pending:
            cut = pending.pop()
            for leaf in cut:
                if leaf not in graph:
                    continue
                expanded = (cut - {leaf}) | frozenset(graph[leaf])
                if expanded not in seen:
                    seen.add(expanded)
                    pending.append(expanded)
        all_cuts[root] = seen

    for k in range(2, 7):
        truth_rows = rows(run(prefix + f'lsv_cut_tt {k}'), 16)
        sizes = rows(run(prefix + f'lsv_cut_bddsize {k}'), 10)
        expected_keys = {(root, tuple(sorted(cut))) for root, cuts in all_cuts.items()
                         for cut in cuts if len(cut) <= k}
        assert set(truth_rows) == expected_keys
        assert set(sizes) == expected_keys
        for (root, cut), truth in truth_rows.items():
            bits = []
            for assignment in itertools.product((0, 1), repeat=len(cut)):
                values = dict(zip(cut, assignment))
                def evaluate(node):
                    if node in values:
                        return values[node]
                    return evaluate(graph[node][0]) & evaluate(graph[node][1])
                bits.append(evaluate(root))
            assert truth == sum(bit << a for a, bit in enumerate(bits))
            assert sizes[root, cut] == bdd_size(bits)
        if k == 6:
            assert any(truth == 1 << 63 for truth in truth_rows.values())

    # A complement of the first input shifts the sole true minterm to bit 31.
    circuit.write_text(circuit.read_text().replace('.names x0 x1 a\n11 1',
                                                  '.names x0 x1 a\n01 1'))
    assert any(truth == 1 << 31 for truth in
               rows(run(prefix + 'lsv_cut_tt 6'), 16).values())
    circuit.write_text('.model constant\n.inputs x\n.outputs y\n.names y\n1\n.end\n')
    assert not rows(run(prefix + 'lsv_cut_tt 6'), 16)
    assert not rows(run(prefix + 'lsv_cut_bddsize 6'), 10)

for command in ['lsv_cut_tt', 'lsv_cut_bddsize']:
    assert 'Empty network' in run(command + ' 3')
    assert 'strash first' in run(f'read {example}; {command} 3')
    for args in ['', '-h', '-z', 'wrong', '1', '7', '3x', '-2', '3 extra',
                 '3.0', '999999999999999999999999999999999999']:
        output = run(f'{command} {args}')
        assert f'usage: {command} [-h] <k>' in output, (command, args, output)
        assert not rows(output, 16), (command, args)

output = run(f'read {example}; strash; lsv_print_nodes')
assert len(re.findall(r'^Object Id = ', output, re.M)) == 3
assert 'usage: lsv_print_nodes [-h]' in run('lsv_print_nodes -h')
print('PASS: example, all k=2..6 cuts, truth tables, BDD sizes, complements, constants, help, errors, and print nodes')
