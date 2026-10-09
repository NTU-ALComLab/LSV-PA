#!/usr/bin/env python3
"""PA1 regressions: test_pa1.py [path/to/abc] [-v | -k pattern].

Add --native to also link the existing Make build objects for non-topological
IDs, CUDD reference checks, and a no-CUDD compilation check.
Stream all supplied benchmarks instead:
  test_pa1.py [path/to/abc] --benchmarks --benchmark-dir PATH
Add --all-nodes to retain dangling logic with strash -ac.
The benchmark timeout and memory limit apply only to the test subprocess.
Elapsed times include loading, strashing, and streamed output.
"""

import argparse
import hashlib
import itertools
import json
import os
import pathlib
import random
import re
import resource
import shlex
import shutil
import subprocess
import sys
import threading
import time
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[3]
ABC = ROOT / "abc"
WORK = ROOT / "src/ext-lsv/tests" / f".work-{os.getpid()}"
COMMANDS = ("lsv_cut_tt", "lsv_cut_bddsize")
DONE = "PA1_COMMAND_COMPLETED"
ROW = re.compile(r"^(\d+):((?: \d+)*): ([0-9A-F]+)$")


def abc(script):
    result = subprocess.run(
        [str(ABC), "-c", script], cwd=ROOT, capture_output=True,
        text=True, timeout=30,
    )
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def fixture(name, inputs, gates, outputs=("out",)):
    path = WORK / f"{name}.blif"
    lines = [f".model {name}", ".inputs " + " ".join(inputs),
             ".outputs " + " ".join(outputs)]
    for output, fanins, cube in gates:
        lines.append(".names " + " ".join((*fanins, output)))
        if cube is not None:
            lines.append(cube)
    path.write_text("\n".join((*lines, ".end", "")))
    return path


def rows(text, bdd=False):
    result = {}
    for line in text.splitlines():
        match = ROW.fullmatch(line)
        if not match:
            if re.match(r"^\d+:", line):
                raise AssertionError(f"Malformed result row: {line!r}")
            continue
        node, leaves, value = match.groups()
        leaves = tuple(map(int, leaves.split()))
        assert tuple(sorted(set(leaves))) == leaves, line
        key = (int(node), leaves)
        assert key not in result, f"Duplicate cut: {line}"
        result[key] = int(value, 10 if bdd else 16)
        assert value == (str(result[key]) if bdd else f"{result[key]:X}"), line
    return result


def graph_from_dot(text):
    """DOT node numbers are ABC object IDs, not the displayed node labels."""
    inputs, nodes, outputs = {}, {}, {}
    for line in text.splitlines():
        match = re.search(r'Node(\d+) \[label = "([^"]*)", shape = (\w+)', line)
        if match:
            ident, label, shape = match.groups()
            ident = int(ident)
            if shape == "triangle":
                inputs[ident] = label
            elif shape == "ellipse":
                nodes[ident] = []
            elif shape == "invtriangle":
                outputs[label] = ident
    edges = {}
    for source, target, style in re.findall(
        r"Node(\d+) -> Node(\d+) \[style = (solid|dotted)\]", text
    ):
        edges.setdefault(int(source), []).append((int(target), style == "dotted"))
    for ident in nodes:
        nodes[ident] = edges[ident]
        assert len(nodes[ident]) == 2
    return inputs, nodes, {name: edges[ident][0] for name, ident in outputs.items()}


def inspect(path, transform="strash"):
    dot = WORK / "graph.dot"
    output = abc(f"read {path}; {transform}; lsv_print_nodes; write_dot {dot}")
    graph = graph_from_dot(dot.read_text())
    # Cross-check the exported graph against the unchanged inspection command.
    printed = {}
    current = None
    for line in output.splitlines():
        match = re.match(r"Object Id = (\d+),", line)
        if match:
            current = int(match[1])
            printed[current] = []
        match = re.match(r"  Fanin-\d+: Id = (\d+),", line)
        if match:
            printed[current].append(int(match[1]))
    assert printed == {node: [child for child, _ in edges]
                       for node, edges in graph[1].items()}
    return graph


def separator_oracle(inputs, nodes, root, k):
    """Enumerate subsets hitting every root-to-PI path, not fanin cut products."""
    def paths(node):
        if node in inputs:
            return [(node,)]
        if node == 0:  # The fixed AIG constant is not a free input.
            return []
        return [(node, *path) for child, _ in nodes[node] for path in paths(child)]

    all_paths = [set(path) for path in paths(root)]
    ancestors = sorted(set().union(*all_paths)) if all_paths else [root]
    minimal = []
    for count in range(min(k, len(ancestors)) + 1):
        for leaves in itertools.combinations(ancestors, count):
            chosen = set(leaves)
            if all(chosen & path for path in all_paths) and not any(
                old < chosen for old in minimal
            ):
                minimal.append(chosen)
    return [tuple(sorted(cut)) for cut in minimal]


def scalar_truth(nodes, root, leaves):
    def evaluate(node, assignment):
        if node in assignment:
            return assignment[node]
        if node == 0:
            return 1
        return all(evaluate(child, assignment) ^ inverted
                   for child, inverted in nodes[node])

    return sum(int(evaluate(root, dict(zip(leaves, values)))) << index
               for index, values in enumerate(itertools.product((0, 1), repeat=len(leaves))))


def bdd_size(truth, width):
    """Independent reduced decision graph with complemented-edge interning."""
    unique, graph = {}, {}

    def build(values, variable):
        if all(value == values[0] for value in values):
            return 1 if values[0] else -1
        half = len(values) // 2
        low, high = build(values[:half], variable + 1), build(values[half:], variable + 1)
        if low == high:
            return low
        sign = 1 if high > 0 else -1
        key = (variable, sign * low, sign * high)
        if key not in unique:
            ident = len(unique) + 2
            unique[key] = ident
            graph[ident] = key[1:]
        return sign * unique[key]

    root = build([(truth >> i) & 1 for i in range(1 << width)], 0)
    seen, pending = set(), [abs(root)]
    while pending:
        ident = pending.pop()
        if ident not in seen:
            seen.add(ident)
            pending.extend(abs(child) for child in graph.get(ident, ()))
    return len(seen)


class CutTests(unittest.TestCase):
    def check_fixture(self, path, transform="strash"):
        inputs, nodes, outputs = inspect(path, transform)
        for k in range(2, 7):
            with self.subTest(fixture=path.stem, k=k):
                expected = {
                    (root, cut): scalar_truth(nodes, root, cut)
                    for root in nodes
                    for cut in separator_oracle(inputs, nodes, root, k)
                }
                for command in COMMANDS:
                    output = abc(f"read {path}; {transform}; {command} {k}; echo {DONE}")
                    self.assertIn("\n" + DONE, output)
                    wanted = (expected if command == COMMANDS[0] else
                              {key: bdd_size(value, len(key[1]))
                               for key, value in expected.items()})
                    self.assertEqual(rows(output, command == COMMANDS[1]), wanted)
        return inputs, nodes, outputs

    def test_exact_example(self):
        path = ROOT / "lsv/pa1/example.blif"
        self.check_fixture(path)
        expected = {
            (5, (5,)): (2, 2), (5, (1, 2)): (0x4, 3),
            (6, (6,)): (2, 2), (6, (2, 3)): (0x8, 3),
            (7, (7,)): (2, 2), (7, (5, 6)): (0x4, 3),
            (7, (2, 3, 5)): (0x2A, 4), (7, (1, 2, 6)): (0x10, 4),
            (7, (1, 2, 3)): (0x30, 3),
        }
        for index, command in enumerate(COMMANDS):
            actual = rows(abc(f"read {path}; strash; {command} 3"), index == 1)
            self.assertEqual(actual, {key: value[index] for key, value in expected.items()})

    def test_dominated_xnor(self):
        path = fixture("xnor", ("x", "y"), [
            ("a", ("x", "y"), "10 1"), ("b", ("x", "y"), "01 1"),
            ("out", ("a", "b"), "00 1"),
        ])
        inputs, nodes, outputs = self.check_fixture(path)
        root, inverted = outputs["out"]
        self.assertFalse(inverted)
        self.assertEqual(len(nodes), 3)
        actual = rows(abc(f"read {path}; strash; lsv_cut_tt 6"))
        leaves = tuple(sorted(inputs))
        self.assertEqual(actual[root, leaves], 9)
        for internal, _ in nodes[root]:
            self.assertNotIn((root, tuple(sorted((*leaves, internal)))), actual)

    def test_reduced_support_and_constants(self):
        for cube, wanted_truth, wanted_size in [("00 1", 3, 2), ("11 1", 0, 1)]:
            path = fixture("reduction", ("x", "y"), [
                ("a", ("x", "y"), "11 1"), ("b", ("x", "y"), "10 1"),
                ("out", ("a", "b"), cube),
            ])
            inputs, _, outputs = self.check_fixture(path)
            key = (outputs["out"][0], tuple(sorted(inputs)))
            self.assertEqual(rows(abc(f"read {path}; strash; lsv_cut_tt 6"))[key],
                             wanted_truth)
            self.assertEqual(rows(abc(f"read {path}; strash; lsv_cut_bddsize 6"), True)[key],
                             wanted_size)

    def test_variable_order(self):
        for inputs, wanted_size in [(("s", "x", "y"), 4), (("x", "y", "s"), 5)]:
            path = fixture("mux", inputs, [
                ("a", ("s", "x"), "11 1"), ("b", ("s", "y"), "01 1"),
                ("out", ("a", "b"), "00 1"),
            ])
            pis, _, outputs = self.check_fixture(path)
            self.assertEqual(list(pis.values()), list(inputs))
            actual = rows(abc(f"read {path}; strash; lsv_cut_bddsize 3"), True)
            self.assertEqual(actual[outputs["out"][0], tuple(sorted(pis))], wanted_size)

    def test_six_leaf_masks(self):
        for cube, truth in [("11 1", 0x8000000000000000), ("01 1", 0x2AAAAAAAAAAAAAAA)]:
            path = fixture("six", tuple("abcdef"), [
                ("ab", ("a", "b"), "11 1"), ("abc", ("ab", "c"), "11 1"),
                ("abcd", ("abc", "d"), "11 1"), ("abcde", ("abcd", "e"), "11 1"),
                ("out", ("abcde", "f"), cube),
            ])
            pis, _, outputs = self.check_fixture(path)
            actual = rows(abc(f"read {path}; strash; lsv_cut_tt 6"))
            self.assertEqual(actual[outputs["out"][0], tuple(sorted(pis))], truth)

    def test_shared_leaves_and_reconvergence(self):
        rng = random.Random(983)
        for number in range(10):
            names, gates = list("abc"), []
            for index in range(5):
                left, right = rng.sample(names, 2)
                name = f"n{index}"
                gates.append((name, (left, right), rng.choice(("00 1", "01 1", "10 1", "11 1"))))
                names.append(name)
            # Keep all constructed logic observable, including shared children.
            path = fixture(f"reconvergent{number}", tuple("abc"), gates, tuple(names[3:]))
            self.check_fixture(path)

    def test_no_internal_roots(self):
        for name, inputs, gates, outputs in [
            ("direct", ("x",), [("out", ("x",), "1 1")], ("out",)),
            ("constants", (), [("zero", (), None), ("one", (), "1")], ("zero", "one")),
            ("no_outputs", ("x",), [], ()),
        ]:
            path = fixture(name, inputs, gates, outputs)
            for command, k in itertools.product(COMMANDS, range(2, 7)):
                text = abc(f"read {path}; strash; {command} {k}; echo {DONE}")
                self.assertIn("\n" + DONE, text)
                self.assertEqual(rows(text, command == COMMANDS[1]), {})

    def test_dangling_nodes(self):
        path = fixture("dangling", ("a", "b", "c"), [
            ("out", ("a", "b"), "10 1"), ("unused", ("b", "c"), "11 1"),
        ])
        _, nodes, _ = self.check_fixture(path, "strash -ac")
        self.assertEqual(len(nodes), 2)

    def test_repeated_calls_preserve_network(self):
        path = ROOT / "lsv/pa1/example.blif"
        before, after = WORK / "before.aig", WORK / "after.aig"
        commands = "; ".join(f"{command} {k}" for command in COMMANDS for k in range(2, 7))
        text = abc(f"read {path}; strash; write_aiger {before}; print_stats; "
                   f"lsv_print_nodes; {commands}; {commands}; print_stats; "
                   f"lsv_print_nodes; write_aiger {after}; echo {DONE}")
        self.assertIn("\n" + DONE, text)
        self.assertEqual(before.read_bytes(), after.read_bytes())
        stats = [line for line in text.splitlines() if "i/o =" in line]
        self.assertEqual(len(stats), 2)
        self.assertEqual(stats[0], stats[1])
        sections = re.findall(r"(Object Id = 5,.*?Fanin-1: Id = 6, name = n6)", text, re.S)
        self.assertEqual(len(sections), 2)
        self.assertEqual(sections[0], sections[1])
        for command in COMMANDS:
            once = abc(f"read {path}; strash; {command} 3")
            twice = abc(f"read {path}; strash; {command} 3; echo SPLIT; {command} 3")
            left, right = twice.split("\nSPLIT", 1)
            self.assertEqual(rows(left, command == COMMANDS[1]), rows(once, command == COMMANDS[1]))
            self.assertEqual(rows(right, command == COMMANDS[1]), rows(once, command == COMMANDS[1]))

    def test_input_diagnostics(self):
        sequential = WORK / "sequential.blif"
        sequential.write_text(".model seq\n.inputs x\n.outputs y\n.latch x y 0\n.end\n")
        example = ROOT / "lsv/pa1/example.blif"
        for command in COMMANDS:
            cases = [
                ("", "3", "Empty network"),
                (f"read {example}; ", "3", "strashed AIG"),
                (f"read {example}; aig; ", "3", "strashed AIG"),
                (f"read {sequential}; strash; ", "3", "combinational"),
            ]
            for argument in ("", "2 3", "2 -h", "-h 2"):
                cases.append(("", argument, "exactly one"))
            for argument in ("x", "2x", "2.0", "0x3", "1", "7", "-1", "+", "-q",
                             '""', '" 2"', '"2 "', "999999999999999999999999",
                             "-999999999999999999999999"):
                cases.append(("", argument, "Invalid k"))
            for prefix, arguments, diagnostic in cases:
                with self.subTest(command=command, arguments=arguments, prefix=prefix):
                    output = abc(f"{prefix}{command} {arguments}; echo {DONE}")
                    self.assertIn(diagnostic, output)
                    # ABC's executable may exit 0 on a command error; the command
                    # dispatcher must nevertheless abort the following command.
                    self.assertNotIn("\n" + DONE, output)
                    self.assertEqual(rows(output, command == COMMANDS[1]), {})
            self.assertIn(f"usage: {command}", abc(f"{command} -h"))


class MultiplierTest(unittest.TestCase):
    def test_all_sixteen_input_pairs(self):
        lines = [
            ".model reference",
            ".inputs a1 a0 b1 b0",
            ".outputs y3 y2 y1 y0",
        ]
        for bit in range(3, -1, -1):
            lines.append(f".names a1 a0 b1 b0 y{bit}")
            for a in range(4):
                for b in range(4):
                    if (a * b) & (1 << bit):
                        lines.append(f"{a:02b}{b:02b} 1")
        lines.append(".end")
        reference = WORK / "reference.blif"
        reference.write_text("\n".join(lines) + "\n")
        output = abc(f"cec lsv/pa1/mul.blif {reference}")
        self.assertIn("Networks are equivalent", output)


class NativeTests(unittest.TestCase):
    @unittest.skipUnless("--native" in sys.argv, "use --native with the Make build objects")
    def test_non_topological_ids_and_cudd_references(self):
        info = subprocess.run(
            ["make", "--no-print-directory", "cmake_info"], cwd=ROOT,
            capture_output=True, text=True, check=True, timeout=30,
        ).stdout

        def setting(name):
            return shlex.split(info.split(f"SEPARATOR_{name}")[1])

        flags = [flag for flag in setting("CXXFLAGS") if flag != "-DNDEBUG"]
        objects = [str(pathlib.Path(source).with_suffix(".o"))
                   for source in setting("SRC")
                   if source not in ("src/base/main/main.c", "src/ext-lsv/lsvCmd.cpp")]
        compiler = shlex.split(os.environ.get("CXX", "c++"))
        common = compiler + ["-I./src", *flags]
        subprocess.run(
            [arg for arg in common if not arg.startswith("-DABC_USE_CUDD")] +
            ["-fsyntax-only", "src/ext-lsv/lsvCmd.cpp"],
            cwd=ROOT, capture_output=True, text=True, check=True, timeout=30,
        )
        executable = WORK / "cut_native"
        built = subprocess.run(
            common + ["src/ext-lsv/tests/cut_native.cpp", *objects,
                      *setting("LIBS"), "-o", str(executable)],
            cwd=ROOT, capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        result = subprocess.run(
            [str(executable)], cwd=ROOT, capture_output=True, text=True, timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("NATIVE_CHECKS_PASSED", result.stdout)
        empty_output = result.stdout.split("EMPTY_NETWORK_PASSED")[0]
        self.assertEqual(rows(empty_output), {})
        match = re.search(r"IDS (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)", result.stdout)
        x, y, z, root, replacement, dangling = map(int, match.groups())
        graph = {root: [(z, False), (replacement, False)],
                 replacement: [(x, False), (y, True)],
                 dangling: [(y, False), (z, False)]}
        self.assertLess(root, replacement)
        cases = re.split(r"CASE (lsv_cut_tt|lsv_cut_bddsize) (\d+)\n", result.stdout)[1:]
        self.assertEqual(len(cases), 30)
        for command, k, output in zip(cases[::3], cases[1::3], cases[2::3]):
            expected = {(node, cut): scalar_truth(graph, node, cut)
                        for node in graph for cut in separator_oracle({x, y, z}, graph, node, int(k))}
            if command == COMMANDS[1]:
                expected = {key: bdd_size(value, len(key[1])) for key, value in expected.items()}
            self.assertEqual(rows(output, command == COMMANDS[1]), expected)


def benchmarks(directory, timeout, memory_mb, all_nodes=False):
    directory.mkdir(parents=True, exist_ok=True)
    results = []

    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (int(timeout) + 1, int(timeout) + 2))

    for name in ("adder", "int2float", "router", "mem_ctrl", "square", "log2", "sqrt", "div"):
        path = ROOT / "lsv/pa1/benchmarks" / f"{name}.blif"
        for k, command in itertools.product(range(2, 7), COMMANDS):
            transform = "strash -ac" if all_nodes else "strash"
            started = time.monotonic()
            process = subprocess.Popen(
                [str(ABC), "-c", f"read {path}; {transform}; print_stats; {command} {k}; echo {DONE}"],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, preexec_fn=limits,
            )
            expired = threading.Event()

            def stop():
                expired.set()
                process.kill()

            timer = threading.Timer(timeout, stop)
            timer.start()
            stopped, memory_exceeded = threading.Event(), threading.Event()
            peak_rss = [0]

            def monitor_memory():
                # macOS does not support a useful RLIMIT_AS. Sample resident
                # memory instead; this is a harness limit, never a cut limit.
                while not stopped.wait(0.25):
                    sample = subprocess.run(
                        ["ps", "-o", "rss=", "-p", str(process.pid)],
                        capture_output=True, text=True, timeout=5,
                    ).stdout.strip()
                    if sample:
                        peak_rss[0] = max(peak_rss[0], int(sample))
                        if int(sample) > memory_mb * 1024:
                            memory_exceeded.set()
                            process.kill()
                            return

            monitor = threading.Thread(target=monitor_memory)
            monitor.start()
            count, complete, valid = 0, False, True
            digest, messages = hashlib.sha256(), []
            try:
                for line in process.stdout:
                    match = ROW.fullmatch(line.rstrip("\n"))
                    if match:
                        root, leaves, value = match.groups()
                        leaf_ids = tuple(map(int, leaves.split()))
                        valid &= leaf_ids == tuple(sorted(set(leaf_ids))) and len(leaf_ids) <= k
                        if command == COMMANDS[0]:
                            truth = int(value, 16)
                            valid &= truth < (1 << (1 << len(leaf_ids))) and value == f"{truth:X}"
                        else:
                            valid &= value.isdecimal() and 1 <= int(value) <= 127
                        digest.update(f"{root}:{leaves}\n".encode())
                        count += 1
                    elif line.strip() == DONE:
                        complete = True
                    elif line.strip():
                        if len(messages) < 20:
                            messages.append(line.rstrip())
                        if re.match(r"^\d+:|^Error:", line):
                            valid = False
                returncode = process.wait()
            finally:
                timer.cancel()
                timer.join()
                stopped.set()
                monitor.join()
                process.stdout.close()
            row = dict(benchmark=name, k=k, command=command, transform=transform, rows=count,
                       elapsed_seconds=round(time.monotonic() - started, 3),
                       completed=complete and returncode == 0 and valid
                       and not expired.is_set() and not memory_exceeded.is_set(),
                       timed_out=expired.is_set(), returncode=returncode,
                       memory_exceeded=memory_exceeded.is_set(), sampled_peak_rss_kib=peak_rss[0],
                       cut_digest=digest.hexdigest(), messages=messages)
            if command == COMMANDS[1] and row["completed"]:
                row["completed"] = (results[-1]["completed"] and count == results[-1]["rows"]
                                    and row["cut_digest"] == results[-1]["cut_digest"])
            results.append(row)
            filename = "benchmarks-all-nodes.json" if all_nodes else "benchmarks.json"
            (directory / filename).write_text(json.dumps(results, indent=2) + "\n")
            print(f"{name:10} k={k} {command:15} {count:10} rows "
                  f"{row['elapsed_seconds']:8.3f}s {'PASS' if row['completed'] else 'FAIL'}",
                  flush=True)
    return all(row["completed"] for row in results)


if __name__ == "__main__":
    arguments = sys.argv[1:]
    if arguments and not arguments[0].startswith("-"):
        ABC = pathlib.Path(arguments.pop(0)).resolve()
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--abc", type=pathlib.Path)
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--benchmarks", action="store_true")
    parser.add_argument("--all-nodes", action="store_true")
    parser.add_argument("--benchmark-dir", type=pathlib.Path)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--memory-mb", type=int, default=4096)
    options, remaining = parser.parse_known_args(arguments)
    if options.abc:
        ABC = options.abc.resolve()
    if options.timeout <= 0 or options.memory_mb <= 0:
        parser.error("--timeout and --memory-mb must be positive")
    if options.all_nodes and not options.benchmarks:
        parser.error("--all-nodes requires --benchmarks")
    if options.benchmarks:
        if not options.benchmark_dir or remaining:
            parser.error("--benchmarks requires --benchmark-dir PATH and no unittest flags")
        sys.exit(0 if benchmarks(options.benchmark_dir, options.timeout,
                                options.memory_mb, options.all_nodes) else 1)
    WORK.mkdir()
    try:
        unittest.main(argv=[sys.argv[0], *remaining])
    finally:
        shutil.rmtree(WORK)
