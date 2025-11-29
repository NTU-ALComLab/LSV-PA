#!/usr/bin/env bash

FILE="$1"
if [[ -z "$FILE" ]]; then echo "Usage: $0 file.blif"; exit 1; fi

pick_abc() {
  for x in ./abc ./bin/abc abc; do
    command -v "$x" >/dev/null 2>&1 && { echo "$(command -v "$x")"; return; }
    [[ -x "$x" ]] && { echo "$x"; return; }
  done
  echo ""
}

ABC_BIN="$(pick_abc)"
if [[ -z "$ABC_BIN" ]]; then
  echo "Could not find abc."
  exit 2
fi

PS_OUT="$("$ABC_BIN" -c "read \"$FILE\"; ps" 2>/dev/null)"

read NPI NPO < <(
  echo "$PS_OUT" | awk '
     { if (match($0, /i\/o *= *([0-9]+)\/ *([0-9]+)/, a))
           { print a[1], a[2]; exit; } }
  '
)

echo "Network: $FILE  PIs=$NPI  POs=$NPO"
echo

extract_class() {
  "$ABC_BIN" -c "$1" \
    | grep -E '^(positive unate|negative unate|independent|binate)$' \
    | head -n1
}

extract_witness() {
  "$ABC_BIN" -c "$1" \
    | grep -E '^(positive unate|negative unate|independent|[01 \-]+)$' \
    | tail -n +2 | head -n 2
}

for ((k=0; k<NPO; k++)); do
  for ((i=0; i<NPI; i++)); do
    C_BDD=$(extract_class "read \"$FILE\"; collapse; lsv_unate_bdd $k $i")
    C_SAT=$(extract_class "read \"$FILE\"; strash;  lsv_unate_sat $k $i")

    printf "PO=%d PI=%d  BDD=%-12s  SAT=%-12s  " $k $i "$C_BDD" "$C_SAT"
    if [[ "$C_BDD" == "$C_SAT" ]]; then
      echo "OK"
    else
      echo "MISMATCH"
      echo "  BDD:"
      extract_witness "read \"$FILE\"; collapse; lsv_unate_bdd $k $i" | sed 's/^/    /'
      echo "  SAT:"
      extract_witness "read \"$FILE\"; strash;  lsv_unate_sat $k $i" | sed 's/^/    /'
    fi
    echo
  done
done
