#!/bin/sh
# Reproduces results.txt. dec.c includes karm.c from the sibling directory
# experiments/fpbs-wedge-k-arm-2026-09-18. Single-threaded, small memory.
set -e
gcc -O2 -o dec dec.c
nice -n 19 ./dec 3
for n in 8 16 32; do nice -n 19 ./dec $n 20000 $n; done
nice -n 19 ./dec 64 5000 64
nice -n 19 ./dec 128 1000 128
