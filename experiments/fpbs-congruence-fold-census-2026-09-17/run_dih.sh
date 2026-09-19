#!/bin/bash
# Virtually abelian control: regular actions of dihedral quotients D_N of F_2.
set -e
cd "$(dirname "$0")"
BIN=$(mktemp -d)/perc
gcc -O2 -o "$BIN" perc.c
run() { echo "== $* (trials=$T prune=$PR)"; python3 gen.py "$@" | "$BIN" "$T" 3 "$PR" 2>/dev/null; }
T=6; PR=1
for mode in 0 1 2; do for N in 100 1000 10000; do run dih $N $mode; done; done
