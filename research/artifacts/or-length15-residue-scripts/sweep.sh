#!/bin/bash
# Run vfib.py on every relator in a word list, in parallel, one output file per word.
# Usage: sweep.sh WORDLIST OUTDIR KMAX RPOT LAM JOBS [KMIN]
set -u
cd "$(dirname "$0")"
L=$1; D=$2; K=$3; R=$4; LAM=$5; J=$6; KMIN=${7:-1}
mkdir -p "$D"
xargs -a "$L" -P "$J" -I{} sh -c "python3.11 vfib.py {} $K $R $LAM $KMIN > $D/{}.out 2>&1"
echo SWEEP_DONE > "$D/SWEEP_DONE"
