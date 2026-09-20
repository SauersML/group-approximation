#!/bin/sh
# Exhaustive census for n = NMIN..NMAX: all involution types k = 0..floor(n/2), in parallel per n.
# Usage: exhaust.sh BINARY NMIN NMAX OUTFILE   (BINARY is gate_exhaust.c compiled with -O2 -I.)
# exhaust_results.txt was produced by: exhaust.sh ./gate_exhaust 3 11 exhaust_results.txt
B="$1"; NMIN="$2"; NMAX="$3"; OUT="$4"
: > "$OUT"
n="$NMIN"
while [ "$n" -le "$NMAX" ]; do
  k=0
  while [ $((2 * k)) -le "$n" ]; do
    "$B" "$n" "$k" > "$OUT.part$k" &
    k=$((k + 1))
  done
  wait
  k=0
  while [ $((2 * k)) -le "$n" ]; do
    cat "$OUT.part$k" >> "$OUT"; rm -f "$OUT.part$k"
    k=$((k + 1))
  done
  n=$((n + 1))
done
