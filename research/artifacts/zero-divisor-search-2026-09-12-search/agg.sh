#!/bin/bash
# Aggregate the shards of one zds array run: agg.sh <n> <array job id>.
# Prints rc failures, graph counts (geng, g6 files, GRAPH lines), survivors, budget hits and node totals.
N=$1; J=$2
cd /scratch.global/sauer354/zds/search/n$N || exit 1
echo "logs $(ls n$N.${J}_*.log | wc -l) without ALLDONE $(grep -L ALLDONE n$N.${J}_*.log | wc -l)"
grep -h "^== r$N" n$N.${J}_*.log | awk '{ for (i = 1; i <= NF; i++) { split($i, kv, "=")
    if (kv[1] == "rc" && kv[2] != 0) bad++; if (kv[1] == "done") d += kv[2]; if (kv[1] == "surv") s += kv[2]
    if (kv[1] == "budget") b += kv[2]; if (kv[1] == "seconds") { t += kv[2]; if (kv[2] > mx) mx = kv[2] } } k++ }
  END { print "shards", k, "rc!=0", bad + 0, "graphs", d, "surv", s + 0, "budget", b + 0, "seconds", t, "max", mx }'
grep -h '^>Z' n$N.${J}_*.log | awk '{ g += $2 } END { print "geng graphs", g }'
echo "g6 lines $(cat g$N.*.g6 | wc -l) duplicates $(cat g$N.*.g6 | sort | uniq -d | wc -l) GRAPH lines $(cat r$N.*.out | grep -c '^GRAPH')"
grep -h '^SURV' r$N.*.out | cut -c1-200 | head
grep -h '^TOTAL' r$N.*.out | awk '{ it += $3; n += $5; c += $10; a += $12; f += $14; p += $16 }
  END { print "items", it, "nodes", n, "coinc", c, "ab", a, "finite", f, "power", p }'
grep -h '^GRAPH' r$N.*.out | awk '{ print $5 }' | sort -n |
  awk '{ a[NR] = $1; t += $1 } END { print "per graph", t / NR, "median", a[int(NR / 2)], "max", a[NR] }'
cat r$N.*.err | sort | uniq -c | head -5
cat n$N.${J}_*.log | md5sum
echo AGGDONE
