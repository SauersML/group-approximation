#!/bin/bash
# Depth-j census: level-m quotients of a o phi^j for the 3- and 5-adic congruence witnesses.
set -e
cd "$(dirname "$0")"
BIN=$(mktemp -d)/perc
gcc -O2 -o "$BIN" perc.c
run() { echo "== $* (trials=$T prune=$PR)"; python3 gen.py "$@" | "$BIN" "$T" 11 "$PR" 2>/dev/null; }
T=8; PR=1
for j in 0 1 2 3; do for m in 9 25 27; do run sl2d $m $j; done; done
