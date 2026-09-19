#!/bin/bash
# ./finish.sh X i : stage X_i emptied block TX. Keep only its K lines (the search then went on with D sweeps outside
# the block, which the chain does not use), rebuild sX_i = sX_{i-1} minus their points, and check sX_i = sX_0 \ TX.
cd "$(dirname "$0")" || exit 1; X=$1; i=$2; p=$((i-1))
nm(){ sed 's/ *$//' "$1" | grep -v '^$' | LC_ALL=C sort; }
[ -s k${X}_$i.full ] || mv k${X}_$i.txt k${X}_$i.full
grep '^K' k${X}_$i.full > k${X}_$i.txt; mv s${X}_$i.txt s${X}_$i.search 2>/dev/null
awk '{k=$2;for(j=3;j<=9;j++)k=k" "$j;print k}' k${X}_$i.txt | LC_ALL=C sort > fin$X.del
LC_ALL=C comm -23 <(nm s${X}_$p.txt) fin$X.del > s${X}_$i.txt
n1=$(wc -l < s${X}_$i.txt); n0=$(( $(wc -l < s${X}_$p.txt) - $(wc -l < k${X}_$i.txt) ))
LC_ALL=C comm -23 <(nm s${X}_0.txt) <(nm T$X.txt) > fin$X.exp
if [ $n1 = $n0 ] && cmp -s s${X}_$i.txt fin$X.exp; then echo "$X stage $i FINISHED: K=$(wc -l < k${X}_$i.txt) end = s${X}_0 minus T$X ($n1 points)"; rm -f fin$X.del fin$X.exp
else echo "$X stage $i NOT FINISHED ($n1 vs $n0; $(LC_ALL=C comm -12 s${X}_$i.txt <(nm T$X.txt) | wc -l) block points left)"; fi
