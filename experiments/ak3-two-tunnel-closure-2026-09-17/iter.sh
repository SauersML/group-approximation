#!/bin/bash
export LC_ALL=C
# iter.sh RANK C2 BASE MDONE NEWSTATES TAG
# One round of the seeded 2-tunnel closure at cap 24:
#  BASE      = current T (states file), MDONE = m classes already processed,
#  NEWSTATES = states added last round (already in the closure under capped moves + tunnels).
# Enumerates the m classes of NEWSTATES (mode A), drops those in MDONE, runs mode B on the rest
# against BASE+NEWSTATES, canonicalises the NEW landings and grows them with grow (capped moves
# and tunnels).  Writes TAG.base, TAG.mdone, TAG.new (states added this round).
R=$1; C2=$2; BASE=$3; MDONE=$4; NEWS=$5; T=$6
nb=$(wc -l < $BASE); nn=$(wc -l < $NEWS)
cat $BASE $NEWS > $T.base
nice -n 10 timeout 1200 ./t2m A $R 24 $C2 $T.base $nb $((nb+nn)) $T.mall > $T.alog; ex=$?; grep DONE $T.alog; [ $ex -ne 0 ] && { echo "A FAILED"; exit 9; }
sort $T.mall > $T.ms; sort $MDONE > $T.md; comm -23 $T.ms $T.md > $T.m; rm -f $T.mall $T.ms
echo "round $T: new states $nn, m classes new $(wc -l < $T.m)"
sort -m $T.md $T.m > $T.mdone; rm -f $T.md
N=$(wc -l < $T.m); CH=${CHUNK:-20000}; : > $T.land
for ((lo=0; lo<N; lo+=CH)); do
  nice -n 10 timeout 1200 ./t2m B $R 24 $C2 $T.base $T.m $lo $((lo+CH)) $T.next.$lo > $T.b.$lo 2>&1
  ex=$?; echo "B chunk $lo exit $ex"; [ $ex -ne 0 ] && { echo "CHUNK FAILED $lo"; exit 9; }; grep -v -E "^NEW|^progress|^HIST" $T.b.$lo
  grep "^NEW" $T.b.$lo | sed 's/.*-> //' >> $T.land; rm -f $T.b.$lo
done
./canon $R < $T.land | sort -u > $T.seeds; rm -f $T.land
echo "landings: $(wc -l < $T.seeds) classes"
nice -n 10 timeout 1200 ./grow $R 24 $T.base $T.seeds $T.new | tail -2
echo "ROUND $T DONE new $(wc -l < $T.new)"
