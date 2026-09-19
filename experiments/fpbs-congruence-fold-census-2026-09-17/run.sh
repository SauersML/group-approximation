#!/bin/bash
# Usage: bash run.sh OUTFILE   (compiles perc.c to a temp binary, runs the census)
set -e
cd "$(dirname "$0")"
BIN=$(mktemp -d)/perc
gcc -O2 -o "$BIN" perc.c
run() { echo "== $* (trials=$T)"; python3 gen.py "$@" | "$BIN" "$T" 7 "$PR" 2>/dev/null; }
T=12; PR=1
for m in 3 5 7 9 11 13 17 19 25 27; do run sl2 $m; done
for n in 500 2000 5000 10000; do run rand $n 1; done
for N in 1000 10000; do run cyc $N 7; done
run prod 7 50
run prod 13 20
T=3; PR=0
for m in 23 29 49 81; do run sl2 $m; done
for n in 50000 200000; do run rand $n 2; done
