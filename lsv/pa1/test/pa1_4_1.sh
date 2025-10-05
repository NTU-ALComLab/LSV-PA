#!/bin/bash

./abc <<'EOF' > pa1_4_logs.txt 2>&1
echo "===== Running mem_ctrl.blif ====="
read ./lsv/pa1/benchmarks/mem_ctrl.blif
strash
lsv_printmocut 6 1

quit
EOF