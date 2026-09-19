#!/bin/bash
# ./segchain3.sh X i : (K) chain for block TX with kzs3, stages X_i, X_{i+1}, ... from sX_{i-1}.txt, until TX is empty
cd "$(dirname "$0")" || exit 1; X=$1; i=${2:-1}
while true; do p=$((i-1))
  nice -n 10 timeout 1200 ../kzs3 8 10 s${X}_$p.txt T$X.txt k${X}_$i.txt s${X}_$i.txt 1000 > k${X}_$i.log 2>&1
  L=$(tail -n 1 k${X}_$i.log); echo "$(date -u +%H:%M:%S) seg $X stage $i (kzs3): $L" >> seg$X.log
  case "$L" in *"BLOCK EMPTY"*) echo DONE >> seg$X.log; break;; *"time budget"*) ;; *) echo END >> seg$X.log; break;; esac
  i=$((i+1))
done
