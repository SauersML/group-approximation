#!/bin/sh
# Exact s = 5 run of rel on one law-6 cover instance, split over 4 processes.
# Usage: sh run_law6.sh REL inst.txt outprefix
REL=$1; INST=$2; OUT=$3
for p in 0 1 2 3; do
  "$REL" "$INST" 5 0 fast $p 4 > "$OUT"_p$p.txt 2>&1 &
done
wait
