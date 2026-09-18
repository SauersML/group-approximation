#!/bin/bash
# band.sh RANK C2 BASE MDONE FRONTIER PREFIX START MAXROUND
# k-tunnel closure in the band (24, C2]: the frontier F holds Whitehead-minimal classes m with
# 24 < |m| <= C2 not yet processed.  Each round runs t2m B on F against BASE; landings are
# canonicalised and grown (grow: capped moves + tunnels); the next frontier is the set of
# next-level classes plus the m classes of the new states (t2m A), minus everything processed.
export LC_ALL=C
R=$1; C2=$2; B=$3; M=$4; F=$5; P=$6; k=$7; KMAX=$8; CH=${CHUNK:-5000}
while [ -s $F ] && [ $k -le $KMAX ]; do
  T=$P$k; N=$(wc -l < $F); : > $T.land; : > $T.nx
  echo "band round $T: frontier $N, base $(wc -l < $B)"
  for ((lo=0; lo<N; lo+=CH)); do
    nice -n 10 timeout 1200 ./t2m B $R 24 $C2 $B $F $lo $((lo+CH)) $T.nxc > $T.b 2>&1; ex=$?
    echo "B chunk $lo exit $ex"; [ $ex -ne 0 ] && { echo "CHUNK FAILED $T $lo"; exit 9; }
    grep -E "^DONE|^GOAL|^PRIM" $T.b | cut -c1-250; grep "^NEW" $T.b | sed 's/.*-> //' >> $T.land; cat $T.nxc >> $T.nx; rm -f $T.b $T.nxc
  done
  sort -m $M <(sort $F) > $T.mdone
  ./canon $R < $T.land | sort -u > $T.seeds; rm -f $T.land
  echo "landings: $(wc -l < $T.seeds) classes"
  nice -n 10 timeout 1200 ./grow $R 24 $B $T.seeds $T.new | tail -2 || exit 9
  nb=$(wc -l < $B); nn=$(wc -l < $T.new); cat $B $T.new > $T.base
  if [ $nn -gt 0 ]; then nice -n 10 timeout 1200 ./t2m A $R 24 $C2 $T.base $nb $((nb+nn)) $T.ma > $T.alog || exit 9; cat $T.ma >> $T.nx; rm -f $T.ma; fi
  sort -u $T.nx | comm -23 - $T.mdone > $T.front; rm -f $T.nx
  echo "BAND ROUND $T DONE new states $nn next frontier $(wc -l < $T.front)"
  B=$T.base; M=$T.mdone; F=$T.front; k=$((k+1))
done
echo "BAND STOP at $P$((k-1)) base $(wc -l < $B) frontier $(wc -l < $F 2>/dev/null)"
