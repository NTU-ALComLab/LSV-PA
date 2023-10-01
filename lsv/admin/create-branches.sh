#!/bin/bash
students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
git switch master
for student in "${students[@]}"; do
    echo "Creating branch ${student} ..."
    git branch "${student}"
    git switch "${student}"
    git push --set-upstream origin "${student}"
done
git switch master
