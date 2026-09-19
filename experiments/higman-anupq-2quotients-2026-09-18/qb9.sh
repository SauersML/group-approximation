#!/bin/sh
# Qbar_B at e=9: relators of Bbar_9 from the level-3 tables, sufficiency check, then pq classes 12..17.
cd "$(dirname "$0")"
PQ=../../../pq_bin
nice -n 10 python3 bbrels.py 9 3 ${NREL:-500} > rels-e9.txt 2> rels-e9.log || exit 1
R=$(paste -sd, rels-e9.txt)
printf '1\nprime 2\nclass 30\noutput 1\ngenerators {b,d}\nrelations {%s};\n0\n' "$R" > bb9.in
nice -n 10 timeout 1800 $PQ -k < bb9.in > bb9.out 2>&1
grep "Group completed" bb9.out || { echo "bb9 did not complete"; exit 2; }
grep -q "Order = 2^22" bb9.out || { echo "bb9 order wrong"; exit 3; }
JMIN=7 ./mk.sh 9 12 17 "{a,b,c,d}" "{ b^a = b^3, c^b = c^3, d^c = d^3, a^d = a^3, a^512, b^512, c^512, d^512, [a,c]^2, $R }" > qb9.in
(nice -n 10 timeout 14000 $PQ -k -s 400000000 < qb9.in) > qb9.out 2>&1
echo "qb9 exit $?"
