#!/bin/sh
# usage: pqgap.sh E CLASS OUTFILE [EXTRA_RELS]  -> GAP pc presentation of largest class-CLASS 2-quotient of Gammabar_E
# PQ = path to the standalone ANUPQ binary (default: pq). Output file defines F in GAP. p3.g, p4.g, p5.g came from: sh pqgap.sh 3 3 p3.g; sh pqgap.sh 4 4 p4.g; sh pqgap.sh 5 7 p5.g
E=$1; C=$2; OUT=$3; X=${4:+, $4}
M=$((1<<E)); rm -f $OUT
printf '1\nprime 2\nclass %s\noutput 0\ngenerators {a,b,c,d}\nrelations { b^a = b^3, c^b = c^3, d^c = d^3, a^d = a^3, a^%s, b^%s, c^%s, d^%s, [a,c]^2 %s};\n8\n25\n%s\n2\n0\n0\n' $C $M $M $M $M "$X" $OUT | nice -n 10 timeout 1200 ${PQ:-pq} -k -s 200000000 | grep -i "order\|error" | tail -2
