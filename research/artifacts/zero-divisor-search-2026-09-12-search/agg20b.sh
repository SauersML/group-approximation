#!/bin/bash
# Aggregate and bundle the second pass at n = 20: agg20b.sh <array job id>.
# Same checks as agg.sh, over n20b.<job>_<i>.log and r20b.<i>.out, with the shard files of ../n20.
set -u
J=$1
D=/scratch.global/sauer354/zds/search/n20b
P=/projects/standard/hsiehph/sauer354/zds-search/n20b
cd "$D" || { echo NO_DIR; echo AGGDONE; exit 1; }
{
echo "logs $(ls n20b.${J}_*.log | wc -l) without ALLDONE $(grep -L ALLDONE n20b.${J}_*.log | wc -l)"
grep -h "^== r20b" n20b.${J}_*.log | awk '{ for (i = 1; i <= NF; i++) { split($i, kv, "=")
    if (kv[1] == "rc" && kv[2] != 0) bad++; if (kv[1] == "done") d += kv[2]; if (kv[1] == "surv") s += kv[2]
    if (kv[1] == "budget") b += kv[2]; if (kv[1] == "seconds") { t += kv[2]; if (kv[2] > mx) mx = kv[2] } } k++ }
  END { print "shards", k, "rc!=0", bad + 0, "graphs", d, "surv", s + 0, "budget", b + 0, "seconds", t, "max", mx }'
echo "g6 lines $(cat ../n20/g20.*.g6 | wc -l) duplicates $(cat ../n20/g20.*.g6 | sort | uniq -d | wc -l) GRAPH lines $(cat r20b.*.out | grep -c '^GRAPH')"
grep -h '^SURV' r20b.*.out | cut -c1-200 | head
grep -h '^TOTAL' r20b.*.out | awk '{ it += $3; n += $5; c += $10; a += $12; f += $14; p += $16 }
  END { print "items", it, "nodes", n, "coinc", c, "ab", a, "finite", f, "power", p }'
grep -h '^GRAPH' r20b.*.out | awk '{ print $5 }' | sort -n |
  awk '{ a[NR] = $1; t += $1 } END { print "per graph", t / NR, "median", a[int(NR / 2)], "max", a[NR] }'
grep -h '^GRAPH' r20b.*.out | awk '{ print $3 }' | sort | uniq -d | wc -l | sed 's/^/duplicate GRAPH lines /'
cat r20b.*.err | sort | uniq -c | head -5
cat n20b.${J}_*.log | md5sum
} > n20b.$J.agg.txt 2>&1
for i in $(seq 0 127); do cat "n20b.${J}_$i.log"; done > n20b.$J.logs.txt
for i in $(seq 0 127); do grep -E '^(GRAPH|TOTAL)' "r20b.$i.out"; done | gzip -9n > r20b.lines.txt.gz
mkdir -p "$P"
cp n20b.$J.logs.txt n20b.$J.agg.txt r20b.lines.txt.gz "$P"/
cat n20b.$J.agg.txt
(cd "$P" && md5sum n20b.$J.logs.txt n20b.$J.agg.txt r20b.lines.txt.gz && ls -l)
echo AGGDONE
