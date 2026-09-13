#!/bin/bash
# job2.sh -- every degenerate principal series at once: l^2_0(F_p^3 minus 0), N = p^3 - 1,
# elements 0, 1, 2 (exact regular norms), arithmetic m = 19, random SL_3(F_p), random permutations.
D=/projects/standard/hsiehph/sauer354/ex/ex2-cubic-ihara-bass
cd "$D" || exit 1
U="0 1 -1 0 -1 -1 -1 -1 -1"
: > cmds2.txt
for p in 29 41 43 71 83 97 113 127 139 167 181 197 211; do
  for e in 0 1 2; do
    echo "./ib run $p $U 19 1 0 $e 800 $p" >> cmds2.txt
    echo "./ib run $p $U 19 1 2 $e 800 $p" >> cmds2.txt
    echo "./ib run $p $U 19 1 3 $e 800 $p" >> cmds2.txt
  done
done
: > res2.txt
xargs -P 8 -I{} sh -c '{}' < cmds2.txt >> res2.txt 2>&1
echo "DONE $(wc -l < cmds2.txt) commands" >> res2.txt
