#!/bin/bash
# ./vpiece.sh tag start cert expected_end : replay cert from start with kzv5 in budgeted pieces, compare end set with expected
cd "$(dirname "$0")"; t=$1; mkdir -p v$t; cp $2 v$t/cur.txt; cp $3 v$t/rem.txt
while true; do
  nice -n 10 timeout 1200 ../kzv5 8 9 v$t/cur.txt v$t/rem.txt v$t/nxt.txt 700 > v$t/log 2>&1; c=$?
  L=$(tail -n 1 v$t/log); echo "$t piece: $L" >> verify.log
  if [ $c = 3 ]; then n=$(echo "$L" | sed 's/.* lines=\([0-9]*\) .*/\1/'); tail -n +$((n+1)) v$t/rem.txt > v$t/r2; mv v$t/r2 v$t/rem.txt; mv v$t/nxt.txt v$t/cur.txt
  elif [ $c = 0 ]; then mv v$t/nxt.txt v$t/cur.txt; break
  else echo "$t FAIL code $c" >> verify.log; exit 1; fi
done
if cmp -s <(LC_ALL=C sort v$t/cur.txt) <(LC_ALL=C sort $4); then echo "$t VERIFIED end set matches ($(wc -l < $4) points)" >> verify.log; rm -rf v$t
else echo "$t END MISMATCH" >> verify.log; exit 1; fi
