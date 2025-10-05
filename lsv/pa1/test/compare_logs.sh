#!/bin/bash
# Compare files between ./log and ./log_ng/log

dir1="./log"
dir2="./log_ng/log"
output_dir="diff_results_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$output_dir"

# Loop through files in dir1
for f in "$dir1"/*; do
    filename=$(basename "$f")
    file2="$dir2/$filename"

    if [ -f "$file2" ]; then
        diff -u "$f" "$file2" > "$output_dir/${filename}.diff"
        if [ -s "$output_dir/${filename}.diff" ]; then
            echo "🔸 Differences found in $filename"
        else
            rm "$output_dir/${filename}.diff"  # remove empty diffs
        fi
    else
        echo "⚠️  File missing in second folder: $filename"
    fi
done

echo "✅ Diff completed. Results are saved in: $output_dir"
