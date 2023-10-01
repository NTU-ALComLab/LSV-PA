#!/bin/bash
students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
for student in "${students[@]}"; do
    git switch "${student}"
    echo "Enable lockdown for branch ${student} ..."
    if [ -f ".github/workflows/lockdown.yml.disabled" ]; then
        mv .github/workflows/lockdown.yml.disabled .github/workflows/lockdown.yml
        git add .github/workflows
        git commit -m "Enable lockdown"
        git push
    else
        echo "[ERROR] Lockdown is NOT disabled!"
        exit 1
    fi
done
git switch master
