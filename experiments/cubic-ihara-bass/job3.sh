#!/bin/bash
# job3.sh -- Tracy--Widom-scale statistics of the extreme nontrivial eigenvalues of A + A^-1 + B + B^-1
# on P^2(F_p), split primes 300 < p < 1000, k = 1500: arithmetic m = 19 and m = 1, three Haar-random
# SL_3(F_p) pairs and three uniformly random permutation pairs of the same N (matched controls).
D=/projects/standard/hsiehph/sauer354/ex/ex2-cubic-ihara-bass
cd "$D" || exit 1
U="0 1 -1 0 -1 -1 -1 -1 -1"
: > cmds3.txt
for p in $(seq 301 999); do
  r=$((p % 7)); { [ $r -eq 1 ] || [ $r -eq 6 ]; } || continue
  [ "$(factor $p | wc -w)" -eq 2 ] || continue
  echo "./ib run $p $U 19 0 0 0 1500 $p" >> cmds3.txt
  echo "./ib run $p $U 1 0 0 0 1500 $p" >> cmds3.txt
  for s in 1 2 3; do
    echo "./ib run $p $U 19 0 2 0 1500 $((p * 10 + s))" >> cmds3.txt
    echo "./ib run $p $U 19 0 3 0 1500 $((p * 10 + s))" >> cmds3.txt
  done
done
: > res3.txt
xargs -P 8 -I{} sh -c '{}' < cmds3.txt >> res3.txt 2>&1
echo "DONE $(wc -l < cmds3.txt) commands" >> res3.txt
