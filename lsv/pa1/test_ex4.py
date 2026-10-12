#!/usr/bin/env python3
"""Independent oracle: graph separator search, scalar simulation, Shannon BDDs."""
import argparse
from functools import lru_cache
import itertools
from pathlib import Path
import random
import re
import subprocess
import tempfile


def run(abc, commands):
    p = subprocess.run([str(abc), '-c', commands], capture_output=True,
                       text=True, timeout=60)
    assert p.returncode == 0, p.stdout + p.stderr
    return p.stdout + p.stderr


def read_graph(text):
    types = {int(i): shape for i, shape in re.findall(
        r'Node(\d+) \[label = .*?shape = (\w+)', text)}
    edges = {}
    for a, b, style in re.findall(
            r'Node(\d+) -> Node(\d+) \[style = (solid|dotted)\]', text):
        edges.setdefault(int(a), []).append((int(b), style == 'dotted'))
    return types, edges


def all_cuts(root, types, edges, k):
    ancestors = set()
    def collect(n):
        if n in ancestors:
            return
        ancestors.add(n)
        for child, _ in edges.get(n, []):
            collect(child)
    collect(root)
    # Constant 1 (ID 0) has no variable.
    candidates = sorted(ancestors - {0})
    result = set()
    for size in range(min(k, len(candidates)) + 1):
        for cut in itertools.combinations(candidates, size):
            boundary = frozenset(cut)
            # Enumerate tree-occurrence stopping choices for this candidate.
            # Reconvergent occurrences may stop/expand differently, producing
            # redundant leaves; these must survive when enumerating ALL cuts.
            @lru_cache(None)
            def stopped_sets(n):
                choices = {frozenset((n,))} if n in boundary else set()
                if n == 0:
                    choices.add(frozenset())
                elif types[n] != 'triangle':
                    a, b = edges[n]
                    choices.update(left | right for left in stopped_sets(a[0])
                                   for right in stopped_sets(b[0]))
                return choices
            if boundary in stopped_sets(root):
                result.add(cut)
    return result


def truth(root, cut, edges):
    bits = []
    for assignment in itertools.product((0, 1), repeat=len(cut)):
        values = dict(zip(cut, assignment))
        def evaluate(n):
            if n in values:
                return values[n]
            if n == 0:
                return 1
            value = 1
            for child, inv in edges[n]:
                value &= evaluate(child) ^ inv
            values[n] = value
            return value
        bits.append(evaluate(root))
    return sum(b << i for i, b in enumerate(bits)), bits


def bdd_size(bits):
    # Complement-edge ROBDD constructed by Shannon expansion, independent of CUDD.
    unique, nodes = {}, {}
    def build(values, level):
        if all(b == values[0] for b in values):
            return int(values[0] == 0)  # regular terminal is 1
        half = len(values) // 2
        low = build(values[:half], level + 1)
        high = build(values[half:], level + 1)
        if low == high:
            return low
        sign = high & 1  # CUDD normalizes its then/high edge
        key = (level, low ^ sign, high ^ sign)
        if key not in unique:
            pointer = 2 * (len(unique) + 1)
            unique[key] = pointer
            nodes[pointer] = key[1:]
        return unique[key] ^ sign
    root = build(bits, 0)
    reached = set()
    def visit(p):
        p &= ~1
        if p in reached:
            return
        reached.add(p)
        if p:
            for child in nodes[p]:
                visit(child)
    visit(root)
    return len(reached)


def rows(text, base):
    result = {}
    for root, leaves, value in re.findall(
            r'^(\d+):([\d ]*): ([0-9A-F]+)$', text, re.M):
        key = (int(root), tuple(map(int, leaves.split())))
        assert key not in result, ('duplicate cut', key)
        result[key] = int(value, base)
    return result


def verify(abc, circuit, tmp):
    graph = tmp / 'graph.dot'
    prefix = f'read {circuit}; strash; '
    run(abc, prefix + f'write_dot {graph}')
    types, edges = read_graph(graph.read_text())
    roots = sorted(n for n, shape in types.items() if shape == 'ellipse' and n != 0)
    checked = 0
    for k in range(2, 7):
        expected_tt, expected_bdd = {}, {}
        for root in roots:
            for cut in all_cuts(root, types, edges, k):
                value, bits = truth(root, cut, edges)
                expected_tt[root, cut] = value
                expected_bdd[root, cut] = bdd_size(bits)
        actual_tt = rows(run(abc, prefix + f'lsv_cut_tt {k}'), 16)
        actual_bdd = rows(run(abc, prefix + f'lsv_cut_bddsize {k}'), 10)
        assert actual_tt == expected_tt, (circuit.name, k, 'TT',
                                          actual_tt.keys() ^ expected_tt.keys())
        assert actual_bdd == expected_bdd, (circuit.name, k, 'BDD',
            [(key, actual_bdd.get(key), v) for key, v in expected_bdd.items()
             if actual_bdd.get(key) != v][:5])
        checked += len(expected_tt)
    print(f'PASS {circuit.name}: {len(roots)} internal nodes, {checked} cuts across k=2..6')
    return checked


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--abc', default=str(Path.home() / 'LSV-PA/abc'))
    parser.add_argument('--mul', type=Path)
    args = parser.parse_args()
    abc = Path(args.abc).resolve()
    rng = random.Random(20261009)
    total = 0
    with tempfile.TemporaryDirectory(prefix='lsv-ex4-') as directory:
        tmp = Path(directory)
        cases = {
            'sample': '.inputs x0 x1 x2\n.outputs y\n.names x0 x1 a\n10 1\n.names x1 x2 b\n11 1\n.names a b y\n10 1\n',
            'six': '.inputs a b c d e f\n.outputs y\n.names a b n0\n11 1\n.names c d n1\n11 1\n.names e f n2\n11 1\n.names n0 n1 n3\n11 1\n.names n3 n2 y\n11 1\n',
            'constant': '.inputs a\n.outputs zero one y\n.names zero\n.names one\n1\n.names a y\n0 1\n',
            'reconverge': '.inputs a b c\n.outputs y\n.names a b n0\n10 1\n.names n0 c n1\n01 1\n.names n0 n1 y\n10 1\n',
        }
        for i in range(20):
            available = [f'x{j}' for j in range(4)]
            body = '.inputs ' + ' '.join(available) + '\n'
            for j in range(7):
                a, b = rng.sample(available, 2)
                name = f'n{j}'
                body += f'.names {a} {b} {name}\n{rng.randrange(2)}{rng.randrange(2)} 1\n'
                available.append(name)
            # Expose every gate so strash does not discard unused branches.
            body += '.outputs ' + ' '.join(available[4:]) + '\n'
            cases[f'random{i:02}'] = body
        for name, body in cases.items():
            circuit = tmp / (name + '.blif')
            circuit.write_text(f'.model {name}\n{body}.end\n')
            total += verify(abc, circuit, tmp)
        if args.mul:
            total += verify(abc, args.mul.resolve(), tmp)
        for cmd, message in [('lsv_cut_tt', 'usage:'), ('lsv_cut_tt 1', 'k must'),
                             ('lsv_cut_tt 7', 'k must'), ('lsv_cut_tt xyz', 'k must'),
                             ('lsv_cut_tt 3', 'Empty network'),
                             ('lsv_cut_bddsize 3', 'Empty network')]:
            assert message in run(abc, cmd), cmd
        sample = tmp / 'sample.blif'
        expected_sample_tt = {
            (5, (5,)): 0x2, (5, (1, 2)): 0x4,
            (6, (6,)): 0x2, (6, (2, 3)): 0x8,
            (7, (7,)): 0x2, (7, (5, 6)): 0x4,
            (7, (2, 3, 5)): 0x2A, (7, (1, 2, 6)): 0x10,
            (7, (1, 2, 3)): 0x30,
        }
        expected_sample_bdd = dict(zip(expected_sample_tt, [2, 3, 2, 3, 2, 3, 4, 4, 3]))
        prefix = f'read {sample}; strash; '
        assert rows(run(abc, prefix + 'lsv_cut_tt 3'), 16) == expected_sample_tt
        assert rows(run(abc, prefix + 'lsv_cut_bddsize 3'), 10) == expected_sample_bdd
        assert 'run strash first' in run(abc, f'read {sample}; lsv_cut_tt 3')
        # Repeat both analyses in one process to catch retained state.
        output = run(abc, f'read {sample}; strash; lsv_cut_tt 3; lsv_cut_bddsize 3; lsv_cut_tt 3')
        assert output.count('5: 5: 2') == 3
    print(f'PASS total: {total} cut truth tables and {total} BDD sizes; argument/state checks')


if __name__ == '__main__':
    main()
