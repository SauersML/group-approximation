#!/bin/sh
# usage: mk.sh E C0 C1 GENS RELS  -> pq input computing class C0, then next classes up to C1, testing a^(2^j)
E=$1; C0=$2; C1=$3; GENS=$4; RELS=$5
M=$((1<<E))
printf '1\nprime 2\nclass %s\noutput 1\ngenerators %s\nrelations %s;\n' $C0 "$GENS" "$RELS"
k=$C0
while :; do
  printf '4\n8\n'
  j=${JMIN:-2}; while [ $j -le $E ]; do printf '23\nx1^%s;\n' $((1<<(j-1))); j=$((j+1)); done
  printf '31\n'
  [ $k -ge $C1 ] && break
  printf '6\n'; k=$((k+1))
done
printf '0\n'
