#!/bin/sh
# Lower exponent-p central tower of Gamma^A2_p, computed in chained ANU pq runs.
# Each run restores the saved pc presentation, computes ONE more class, and saves it,
# so every process stays under the 1200 s limit.  Usage: pqchain.sh <pq> p startclass endclass workdir
pq=$1; p=$2; c0=$3; c1=$4; W=$5; cd "$W" || exit 1
printf '1\nG\n%s\n%s\n1\n{a, b, c}\n{a^%s, b^%s, c^%s, [a,b,a], [a,b,b], [b,c,b], [b,c,c], [a,c,a], [a,c,c]}\n0\n\n2\np%sc%s.pcp\n0\n' \
  $p $c0 $p $p $p $p $c0 | nice -n 10 timeout 1200 "$pq" | grep -E "has order|took"
c=$c0
while [ $c -lt $c1 ]; do
  n=$((c+1))
  printf '3\np%sc%s.pcp\n6\n2\np%sc%s.pcp\n0\n' $p $c $p $n | nice -n 10 timeout 1200 "$pq" | grep -E "has order|took" || { echo "class $n: killed or failed"; exit 1; }
  rm -f p${p}c${c}.pcp; c=$n
done
