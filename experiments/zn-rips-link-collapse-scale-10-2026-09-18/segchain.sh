#!/bin/bash
# segment chain for (8,10): ./segchain.sh X [i]; stages X_i from sX_{i-1}.txt, K only at points of TX.txt
cd "$(dirname "$0")" || exit 1; X=$1; i=${2:-1}
while true; do p=$((i-1))
  KZ_KFIRST=1 KZ_KSEL=1 KZ_KLIST=T$X.txt nice -n 10 timeout 1200 ../kzs2 8 10 s${X}_$p.txt s${X}_$i.txt k${X}_$i.txt 1100 > k${X}_$i.log 2>&1
  L=$(tail -n 1 k${X}_$i.log); echo "$(date -u +%H:%M:%S) seg $X stage $i: $L" >> seg$X.log
  case "$L" in *REACHES*) echo DONE >> seg$X.log; break;; *"time budget"*) ;; *) echo END >> seg$X.log; break;; esac
  i=$((i+1))
done
