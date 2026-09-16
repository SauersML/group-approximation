#!/bin/bash
# Sequential virtual-fibring search (research/artifacts/or-length15-residue-scripts/vfib.py) over a
# word list, one word per line.  Every CERT line is then re-checked by verify.py (separately).
# Usage: vfwords.sh WORDS_FILE KMAX KMIN PER_WORD_TIMEOUT OUT
set -u -o pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
S=$HERE/../../research/artifacts/or-length15-residue-scripts
W=$1; K=$2; KMIN=$3; T=$4; OUT=$5
: > "$OUT"
while read -r w; do
  [ -z "$w" ] && continue
  timeout "$T" python3 "$S/vfib.py" "$w" "$K" 1 2 "$KMIN" | grep -v SENTINEL_DONE >> "$OUT" || echo "TIMEOUT $w k=$KMIN..$K" >> "$OUT"
done < "$W"
echo SWEEP_DONE >> "$OUT"
