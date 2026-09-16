#!/bin/bash
# Sequential virtual-fibring sweep (research/artifacts/or-length15-residue-scripts/vfib.py) over the
# length-16 classes left open by primcert.py, then the independent verifier verify.py on every CERT.
# Usage: vfsweep.sh PRIMCERT_OUT KMAX PER_WORD_TIMEOUT OUT
set -u -o pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
S=$HERE/../../research/artifacts/or-length15-residue-scripts
P=$1; K=$2; T=$3; OUT=$4
: > "$OUT"
awk '$1=="NONPRIM"{print $2} $1=="VERDICT" && $NF!="PASS"{print $3}' "$P" | while read -r w; do
  timeout "$T" python3 "$S/vfib.py" "$w" "$K" 1 2 | grep -v SENTINEL_DONE >> "$OUT" || echo "TIMEOUT $w k<=$K" >> "$OUT"
done
echo SWEEP_DONE >> "$OUT"
