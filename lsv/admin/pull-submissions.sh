git fetch
students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
for student in "${students[@]}"; do
    echo "Pulling submission of ${student} ..."
    git sw "${student}"
    git pull
done
git sw master
