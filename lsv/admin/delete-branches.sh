#!/bin/bash
students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
git switch master
for student in "${students[@]}"; do
    echo "Deleting branch ${student} ..."
    git branch -d "${student}"
    git push origin --delete "${student}"
done
