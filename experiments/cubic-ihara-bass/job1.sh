#!/bin/bash
# job1.sh -- nonlinear elements (elem 1-4) on P^2(F_p), split primes 300 < p < 1000:
# arithmetic m = 19 and m = 1, Haar-random SL_3(F_p) pair, uniformly random permutations.
D=/projects/standard/hsiehph/sauer354/ex/ex2-cubic-ihara-bass
cd "$D" || exit 1
U="0 1 -1 0 -1 -1 -1 -1 -1"
: > cmds1.txt
for p in $(seq 301 999); do
  r=$((p % 7)); { [ $r -eq 1 ] || [ $r -eq 6 ]; } || continue
  [ "$(factor $p | wc -w)" -eq 2 ] || continue
  for e in 1 2 3 4; do
    echo "./ib run $p $U 19 0 0 $e 1000 $p" >> cmds1.txt
    echo "./ib run $p $U 1 0 0 $e 1000 $p" >> cmds1.txt
    echo "./ib run $p $U 19 0 2 $e 1000 $p" >> cmds1.txt
    echo "./ib run $p $U 19 0 3 $e 1000 $p" >> cmds1.txt
  done
done
: > res1.txt
xargs -P 8 -I{} sh -c '{}' < cmds1.txt >> res1.txt 2>&1
echo "DONE $(wc -l < cmds1.txt) commands" >> res1.txt
