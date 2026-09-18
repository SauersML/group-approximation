#!/bin/bash
# loop.sh RANK C2 BASE MDONE NEWS PREFIX START -> iterate iter.sh until a round adds no state
R=$1; C2=$2; B=$3; M=$4; N=$5; P=$6; k=$7
while [ -s $N ]; do
  ./iter.sh $R $C2 $B $M $N $P$k || { echo "ROUND FAILED $P$k"; exit 9; }
  B=$P$k.base; M=$P$k.mdone; N=$P$k.new; k=$((k+1))
done
echo "LOOP CLOSED at round $P$((k-1)) base $(wc -l < $B)"
