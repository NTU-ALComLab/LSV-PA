students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
for student in "${students[@]}"; do
    echo "Updating branch ${student} ..."
    git sw "${student}"
    git merge master -m "Merge master into ${student}"
    git push
done
git sw master
