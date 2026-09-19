#!/bin/bash
# ./vpiece6.sh tag start cert expected_end : replay cert from start with kzv6 8 10 in budgeted pieces,
# then compare the end set with expected_end (sorted, whitespace-normalised)
cd "$(dirname "$0")" || exit 1; t=$1; mkdir -p v$t; cp $2 v$t/cur.txt; cp $3 v$t/rem.txt
while true; do
  nice -n 10 timeout 1200 ./kzv6 8 10 v$t/cur.txt v$t/rem.txt v$t/nxt.txt 1000 > v$t/log 2>&1; c=$?
  L=$(tail -n 1 v$t/log); echo "$(date -u +%H:%M:%S) $t piece: $L" >> verify.log
  if [ $c = 3 ]; then n=$(echo "$L" | sed 's/.* lines=\([0-9]*\) .*/\1/'); tail -n +$((n+1)) v$t/rem.txt > v$t/r2; mv v$t/r2 v$t/rem.txt; mv v$t/nxt.txt v$t/cur.txt
  elif [ $c = 0 ]; then mv v$t/nxt.txt v$t/cur.txt; break
  else echo "$t FAIL code $c" >> verify.log; exit 1; fi
done
nm(){ sed 's/ *$//' "$1" | grep -v '^$' | LC_ALL=C sort; }
if cmp -s <(nm v$t/cur.txt) <(nm $4); then echo "$t VERIFIED end set matches ($(wc -l < $4) points)" >> verify.log; rm -rf v$t
else echo "$t END MISMATCH" >> verify.log; exit 1; fi
