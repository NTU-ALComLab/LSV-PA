#!/bin/bash
students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
for student in "${students[@]}"; do
    echo "Updating branch ${student} ..."
    git switch "${student}"
    if git merge master -m "Merge master into ${student}" -X theirs ; then
        git push
    else
        echo "[ERROR] Automatic merging failed! Fix the conflicts and re-run the script."
        exit 1
    fi
done
git switch master
