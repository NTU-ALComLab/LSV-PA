#!/bin/bash
git fetch
students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
for student in "${students[@]}"; do
    echo "Pulling submission of ${student} ..."
    git switch "${student}"
    if git pull ; then
        echo "[INFO] Successfully pulled submission ${student}"
    else
        echo "[ERROR] Pull failed! Fix the conflicts and re-run the script."
        exit 1
    fi
done
git switch master
