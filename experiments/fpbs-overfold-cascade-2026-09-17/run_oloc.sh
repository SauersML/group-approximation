#!/bin/sh
# (O-loc) runs.  Usage: sh run_oloc.sh   (from any directory)
D=$(dirname "$0")
O=$D/oloc_results.txt
: > $O
for k in 2 3 4; do
  for r in 0 1 2; do
    python3 $D/oloc.py $D/model_j1.txt 100000 $k $r 3000 $k$r >> $O
  done
done
for k in 2 3; do
  for r in 0 1; do
    python3 $D/oloc.py $D/model_j2.txt 100000 $k $r 3000 2$k$r >> $O
  done
done
