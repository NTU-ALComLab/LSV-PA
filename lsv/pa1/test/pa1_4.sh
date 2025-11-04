#!/bin/bash

./abc <<'EOF' > pa1_4_logs.txt 2>&1
echo "===== Running adder.blif ====="
read ./lsv/pa1/benchmarks/adder.blif
strash
lsv_printmocut 6 2

echo "===== Running div.blif ====="
read ./lsv/pa1/benchmarks/div.blif
strash
lsv_printmocut 6 2

echo "===== Running int2float.blif ====="
read ./lsv/pa1/benchmarks/int2float.blif
strash
lsv_printmocut 6 2

echo "===== Running log2.blif ====="
read ./lsv/pa1/benchmarks/log2.blif
strash
lsv_printmocut 6 2

echo "===== Running mem_ctrl.blif ====="
read ./lsv/pa1/benchmarks/mem_ctrl.blif
strash
lsv_printmocut 6 2

echo "===== Running router.blif ====="
read ./lsv/pa1/benchmarks/router.blif
strash
lsv_printmocut 6 2

echo "===== Running sqrt.blif ====="
read ./lsv/pa1/benchmarks/sqrt.blif
strash
lsv_printmocut 6 2

echo "===== Running square.blif ====="
read ./lsv/pa1/benchmarks/square.blif
strash
lsv_printmocut 6 2

quit
EOF