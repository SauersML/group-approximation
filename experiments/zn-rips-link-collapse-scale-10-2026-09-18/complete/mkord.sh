#!/bin/bash
# ./mkord.sh X i : ord/sX_i.txt = the points of sX_i.txt in the order of sA_0.txt (the order of O),
# used only as the verifier's scan order; checked equal as a set to sX_i.txt
cd "$(dirname "$0")" || exit 1; X=$1; i=$2; o=ord/s${X}_$i.txt; [ -s $o ] && exit 0
awk 'NR==FNR{k=$1;for(j=2;j<=8;j++)k=k" "$j;d[k]=1;next}{k=$1;for(j=2;j<=8;j++)k=k" "$j;if(k in d)print}' s${X}_$i.txt sA_0.txt > $o.tmp
nm(){ sed 's/ *$//' "$1" | grep -v '^$' | LC_ALL=C sort; }
cmp -s <(nm $o.tmp) <(nm s${X}_$i.txt) && mv $o.tmp $o || { echo "mkord $X $i MISMATCH"; rm -f $o.tmp; exit 1; }
