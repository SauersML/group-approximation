#!/bin/sh
# (O-loc) on small random levels (whole Q is the ball): closures see cycles.
D=$(dirname "$0")
O=$D/oloc_small_results.txt
: > $O
for n in 6 8 12 20; do
  for k in 2 3; do
    python3 $D/oloc.py $D/model_j1.txt $n $k 20 300 9$n$k >> $O
    python3 $D/oloc.py $D/model_j1.txt $n $((k-1)) 20 200 6$n$k 1 >> $O
  done
done
for n in 5 8 12; do
  python3 $D/oloc.py $D/model_j2.txt $n 2 20 200 5$n >> $O
  python3 $D/oloc.py $D/model_j2.txt $n 1 20 200 4$n 1 >> $O
done
