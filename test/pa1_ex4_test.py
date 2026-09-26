#!/usr/bin/env python3
"""Small end-to-end check for the PA1 Exercise 4 commands."""

import re
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def run(circuit, mode, k):
    output = subprocess.check_output(
        [str(ROOT / "abc"), "-c", f"read {circuit}; strash; lsv cut {mode} {k}"],
        text=True,
        cwd=ROOT,
    )
    return [line for line in output.splitlines() if re.fullmatch(r"\d+: [\d ]+: [0-9A-F]+", line)]


example = ROOT / "lsv/pa1/example.blif"
assert run(example, "tt", 3) == [
    "5: 5: 2", "5: 1 2: 4", "6: 6: 2", "6: 2 3: 8", "7: 7: 2",
    "7: 5 6: 4", "7: 2 3 5: 2A", "7: 1 2 6: 10", "7: 1 2 3: 30",
]
assert run(example, "bddsize", 3) == [
    "5: 5: 2", "5: 1 2: 3", "6: 6: 2", "6: 2 3: 3", "7: 7: 2",
    "7: 5 6: 3", "7: 2 3 5: 4", "7: 1 2 6: 4", "7: 1 2 3: 3",
]
assert len(run(example, "tt", 2)) == 6

with tempfile.TemporaryDirectory() as directory:
    circuit = Path(directory) / "six_inputs.blif"
    circuit.write_text(
        ".model six_inputs\n.inputs a b c d e f\n.outputs y\n"
        ".names a b c d e f y\n111111 1\n.end\n"
    )
    assert any(line.endswith(": 8000000000000000") for line in run(circuit, "tt", 6))
    assert any(line.endswith(": 7") for line in run(circuit, "bddsize", 6))

print("PA1 Exercise 4 checks passed")
