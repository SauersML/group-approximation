#!/bin/sh
# Reproduces results.txt (single-threaded, < 50 MB). margin.c = w21-123 wind.c + margin statistics.
set -e
gcc -O2 -o margin margin.c -lm
for n in 8 16 32; do nice -n 10 ./margin $n 20000 $n; done
nice -n 10 ./margin 64 10000 64
nice -n 10 ./margin 128 4000 128
nice -n 10 ./margin 256 800 256
