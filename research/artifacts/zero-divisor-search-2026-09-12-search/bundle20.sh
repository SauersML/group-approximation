#!/bin/bash
# Bundle the n = 20 run for landing: concatenated shard logs, agg.sh output, GRAPH and TOTAL lines.
# Copies the bundle to /projects so it survives scratch purges.
set -u
J=595808
D=/scratch.global/sauer354/zds/search/n20
P=/projects/standard/hsiehph/sauer354/zds-search/n20
cd "$D" || { echo NO_DIR; echo DONE; exit 1; }
for i in $(seq 0 127); do cat "n20.${J}_$i.log"; done > n20.$J.logs.txt
bash /projects/standard/hsiehph/sauer354/zds-search/agg.sh 20 $J > n20.$J.agg.txt 2>&1
for i in $(seq 0 127); do grep -E '^(GRAPH|TOTAL)' "r20.$i.out"; done | gzip -9n > r20.lines.txt.gz
mkdir -p "$P"
cp n20.$J.logs.txt n20.$J.agg.txt r20.lines.txt.gz zds20.c "$P"/
cat n20.$J.agg.txt
gzip -dc r20.lines.txt.gz | awk '{ print $1 }' | sort | uniq -c
(cd "$P" && md5sum n20.$J.logs.txt n20.$J.agg.txt r20.lines.txt.gz zds20.c && ls -l)
echo DONE
