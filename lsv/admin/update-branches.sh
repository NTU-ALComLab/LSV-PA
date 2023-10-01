#!/bin/bash
students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
for student in "${students[@]}"; do
    echo "Updating branch ${student} ..."
    git switch "${student}"
    if git merge master -m "Merge master into ${student}" -X theirs ; then
        if git push ; then
            echo "[INFO] Successfully pushed to branch ${student}."
        else
            echo "[ERROR] Push failed! Please fix possible bad objects and push again."
            exit 1
        fi
    else
        echo "[ERROR] Automatic merging failed! Fix the conflicts and re-run the script."
        exit 1
    fi
done
git switch master
