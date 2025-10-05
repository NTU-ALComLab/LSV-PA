#!/bin/bash
students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
for student in "${students[@]}"; do
    git switch "${student}"
    echo "Disable lockdown for branch ${student} ..."
    if [ -f ".github/workflows/lockdown.yml" ]; then
        mv .github/workflows/lockdown.yml .github/workflows/lockdown.yml.disabled
        git add .github/workflows
        git commit -m "Disable lockdown"
        git push
    else
        echo "[ERROR] Lockdown is NOT enabled!"
        exit 1
    fi
done
git switch master
