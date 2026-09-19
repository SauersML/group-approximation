#!/bin/sh
# (O-loc) mixed runs: k overfold seeds plus l lawful seeds in one ball.
D=$(dirname "$0")
O=$D/oloc_mixed_results.txt
: > $O
for kl in "1 1" "2 1" "3 1" "2 2"; do
  set -- $kl
  for r in 0 1; do
    python3 $D/oloc.py $D/model_j1.txt 100000 $1 $r 1000 7$1$2$r $2 >> $O
  done
done
for kl in "1 1" "2 1"; do
  set -- $kl
  for r in 0 1; do
    python3 $D/oloc.py $D/model_j2.txt 100000 $1 $r 1000 8$1$2$r $2 >> $O
  done
done
