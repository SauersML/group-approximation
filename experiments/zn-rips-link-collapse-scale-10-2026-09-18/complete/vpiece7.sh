#!/bin/bash
# ./vpiece7.sh tag start cert expected_end : replay cert from start with kzv7 8 10 in budgeted pieces,
# then compare the end set with expected_end (sorted, whitespace-normalised)
cd "$(dirname "$0")" || exit 1; t=$1; mkdir -p w$t; cp $2 w$t/cur.txt; cp $3 w$t/rem.txt
nm(){ sed 's/ *$//' "$1" | grep -v '^$' | LC_ALL=C sort; }
# on a pause the next piece keeps the start file's point order (the verifier's scan order), minus the points
# already deleted; this set is checked equal to the verifier's own sorted output before continuing
while true; do
  nice -n 10 timeout 1200 ./kzv7 8 10 w$t/cur.txt w$t/rem.txt w$t/nxt.txt 1000 > w$t/log 2>&1; c=$?
  L=$(tail -n 1 w$t/log); echo "$(date -u +%H:%M:%S) $t piece: $L" >> verify7.log
  if [ $c = 3 ]; then n=$(echo "$L" | sed 's/.* lines=\([0-9]*\) .*/\1/'); head -n $n w$t/rem.txt | awk 'NR==FNR{k=$2;for(i=3;i<=9;i++)k=k" "$i;d[k]=1;next}{k=$1;for(i=2;i<=8;i++)k=k" "$i;if(!(k in d))print}' - w$t/cur.txt > w$t/c2
    tail -n +$((n+1)) w$t/rem.txt > w$t/r2; mv w$t/r2 w$t/rem.txt; mv w$t/c2 w$t/cur.txt
    cmp -s <(nm w$t/cur.txt) <(nm w$t/nxt.txt) || { echo "$t ORDER-KEEP MISMATCH" >> verify7.log; exit 1; }
  elif [ $c = 0 ]; then mv w$t/nxt.txt w$t/cur.txt; break
  else echo "$t FAIL code $c" >> verify7.log; exit 1; fi
done
nm(){ sed 's/ *$//' "$1" | grep -v '^$' | LC_ALL=C sort; }
if cmp -s <(nm w$t/cur.txt) <(nm $4); then echo "$t VERIFIED end set matches ($(wc -l < $4) points)" >> verify7.log; rm -rf w$t
else echo "$t END MISMATCH" >> verify7.log; exit 1; fi
