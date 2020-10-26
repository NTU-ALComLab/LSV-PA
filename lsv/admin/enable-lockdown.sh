students=( $(cut -d, -f1 < lsv/admin/participants-id.csv | tail -n +3) )
for student in "${students[@]}"; do
    git sw "${student}"
    echo "Enable lockdown for branch ${student} ..."
    if [ -f ".github/workflows/lockdown.yml.disabled" ]; then
        mv .github/workflows/lockdown.yml.disabled .github/workflows/lockdown.yml
        git a .github/workflows
        git cm "Enable lockdown"
        git push
    else
        echo "[ERROR] Lockdown is NOT disabled!"
        exit 1
    fi
done
git sw master
