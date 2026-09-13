#!/bin/bash
# job4.sh -- characteristic-polynomial coincidences among cyclically reduced words, n = 2..12:
# arithmetic pair m = 1 and m = 19 (integer f_w via two primes) against a Haar-random SL_3(F_P) pair.
D=/projects/standard/hsiehph/sauer354/ex/ex2-cubic-ihara-bass
cd "$D" || exit 1
U="0 1 -1 0 -1 -1 -1 -1 -1"
: > res4.txt
for n in 2 3 4 5 6 7 8 9 10 11 12; do
  for a in "1 0" "19 0" "19 2"; do
    ./cp run $n $U $a >> res4.txt 2>&1
  done
done
echo "DONE" >> res4.txt
