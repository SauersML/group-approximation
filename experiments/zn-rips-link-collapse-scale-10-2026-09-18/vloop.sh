#!/bin/bash
# verify finished stages of segment $1 in order with kzv6 (vpiece6.sh)
cd "$(dirname "$0")" || exit 1; X=$1; i=1
while true; do
  if [ -s s${X}_$i.txt ] && grep -q "seg $X stage $i:" seg$X.log 2>/dev/null; then
    (cd .. && ./vpiece6.sh ${X}$i sg/s${X}_$((i-1)).txt sg/k${X}_$i.txt sg/s${X}_$i.txt) || { echo "stage $i FAILED" >> vloop$X.log; exit 1; }
    echo "$(date -u +%H:%M:%S) stage $i verified" >> vloop$X.log; i=$((i+1))
  else sleep 30; fi
done
