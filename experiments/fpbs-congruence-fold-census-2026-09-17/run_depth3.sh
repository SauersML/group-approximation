#!/bin/bash
# 5-adic level 125 (n = 1875000) at depths j = 0, 3, 5; one unpruned greedy trial each.
set -e
cd "$(dirname "$0")"
BIN=$(mktemp -d)/perc
gcc -O2 -o "$BIN" perc.c
run() { echo "== $* (trials=$T prune=$PR)"; python3 gen.py "$@" | "$BIN" "$T" 11 "$PR" 2>/dev/null; }
T=1; PR=0
for j in 0 5 3; do run sl2d 125 $j; done
