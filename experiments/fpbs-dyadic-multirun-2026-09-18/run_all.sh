#!/bin/sh
# True coverage decorrelation K = qS/(qA qB) on sparse dyadic patterns of the
# straight Z^2 path (critical box proxy), see
# research/fpbs-bisector-split-chain-caps-at-inverse-theta-squared.md.
# Columns: J qS qA qB K K*theta se(K) se(K*theta).
# The bisector chain's exact output at J=1 (Theorem A) is 1/(qA qB).
set -e
cd "$(dirname "$0")"
gcc -O2 -o dyadic dyadic.c -lm
nice -n 10 timeout 1200 ./dyadic 0.5 32 20000 1 2 5
nice -n 10 timeout 1200 ./dyadic 0.5 64 40000 13 2 5
nice -n 10 timeout 1200 ./dyadic 0.5 128 30000 11 2 6
nice -n 10 timeout 1200 ./dyadic 0.5 128 30000 12 4 3
rm -f dyadic
