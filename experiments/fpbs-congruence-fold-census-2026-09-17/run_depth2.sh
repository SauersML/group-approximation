#!/bin/bash
# Depth continuation: 5-adic level 25, j = 4..8 (pruned, 6 trials).
# (A pruned run at level 49 was started after these and stopped as too slow;
#  level 125 is in run_depth3.sh.)
set -e
cd "$(dirname "$0")"
BIN=$(mktemp -d)/perc
gcc -O2 -o "$BIN" perc.c
run() { echo "== $* (trials=$T prune=$PR)"; python3 gen.py "$@" | "$BIN" "$T" 11 "$PR" 2>/dev/null; }
T=6; PR=1
for j in 4 5 6 7 8; do run sl2d 25 $j; done
