#!/bin/sh
# Reproduces results.txt (single-threaded, < 50 MB).
set -e
gcc -O2 -o wind wind.c -lm
for n in 4 8 16; do nice -n 10 ./wind $n 40000 $n; done
nice -n 10 ./wind 32 40000 32
nice -n 10 ./wind 64 20000 64
nice -n 10 ./wind 128 10000 128
nice -n 10 ./wind 256 1500 256
