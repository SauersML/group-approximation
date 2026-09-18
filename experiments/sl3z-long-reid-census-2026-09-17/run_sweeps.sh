#!/bin/sh
# usage: run_sweeps.sh BIN m R OUTDIR k1 k2 ...
# Runs run_dirs.py for each k sequentially; writes OUTDIR/dirs_k<k>_m<m>_R<R>.out
BIN=$1; M=$2; R=$3; OUT=$4; shift 4
HERE=$(dirname "$0")
for k in "$@"; do
  python3 "$HERE/run_dirs.py" "$BIN" "$k" "$M" "$R" 4 > "$OUT/dirs_k${k}_m${M}_R${R}.out"
done
echo DONE
