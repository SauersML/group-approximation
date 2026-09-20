#!/bin/sh
# Sweep for gate_anneal: n, mark floor M0, four seeds, 3000*n annealing steps, penalty 4.
# Usage: sweep.sh BINARY OUTFILE
B="$1"; OUT="$2"
: > "$OUT"
for n in 32 64 128 256 512; do
  for m0 in 0.10 0.25; do
    for seed in 1 2 3 4; do
      "$B" "$n" "$seed" $((3000 * n)) "$m0" 4 >> "$OUT" &
    done
    wait
  done
done
