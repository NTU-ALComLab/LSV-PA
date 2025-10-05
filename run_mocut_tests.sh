#!/bin/bash
# ============================================================
# Script: run_mocut_tests.sh
# Author: Alex
# Purpose: Iterate all .blif files in benchmarks folder and run lsv_printmocut
# ============================================================

# === 路徑設定 ===
ABC_BIN=~/code/LSV-PA/abc                                  # ABC 執行檔
BENCH_DIR=~/code/LSV-PA/lsv/pa1/benchmarks                 # .blif 檔案所在資料夾
OUTPUT_DIR=~/code/LSV-PA/results_mocut                     # 結果輸出資料夾

# === 建立輸出資料夾（若不存在） ===
mkdir -p "$OUTPUT_DIR"

# === K 與 L 的迭代組合 ===
K_VALUES=(3 4)
L_VALUES=(2 3)

# === 主迴圈：對每個 .blif 檔案執行測試 ===
for file in "$BENCH_DIR"/*.blif; do
    base=$(basename "$file" .blif)
    echo "🔹 Processing $base.blif ..."
    
    for k in "${K_VALUES[@]}"; do
        for l in "${L_VALUES[@]}"; do
            out_file="$OUTPUT_DIR/${base}_k${k}_l${l}.txt"
            echo "  ➤ Running lsv_printmocut $k $l ..."
            
            # 執行 ABC 命令
            "$ABC_BIN" -c "
                read $file;
                strash;
                lsv_printmocut $k $l;
                quit;
            " > "$out_file"
        done
    done
done

echo "✅ All runs finished. Results saved in: $OUTPUT_DIR/"
