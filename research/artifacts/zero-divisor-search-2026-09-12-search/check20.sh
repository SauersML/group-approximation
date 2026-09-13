#!/bin/bash
# Extra invariants of the n = 20 run: every input graph has exactly one GRAPH line, every GRAPH line
# has surv 0, every TOTAL line has fails 0 and budget 0 with the same options, and stderr is empty.
set -u
cd /scratch.global/sauer354/zds/search/n20 || { echo NO_DIR; echo DONE; exit 1; }
T=$(mktemp -d /scratch.global/sauer354/zds/search/check20.XXXX)
cat g20.*.g6 | sort > "$T/in"
grep -h '^GRAPH' r20.*.out | awk '{ print $3 }' | sort > "$T/out"
echo "input $(wc -l < "$T/in") graphed $(wc -l < "$T/out") distinct $(uniq "$T/out" | wc -l)"
if cmp -s "$T/in" "$T/out"; then echo "INPUT_EQ_GRAPHED yes"; else echo "INPUT_EQ_GRAPHED NO"; fi
grep -h '^GRAPH' r20.*.out | awk '$4 != "nodes" || $6 != "surv" || $7 != 0 || $5 <= 0 { bad++ } END { print "GRAPH lines not surv 0 or no nodes", bad + 0 }'
grep -h '^GRAPH' r20.*.out | awk '{ print $8, $9 }' | sort | uniq -c
echo "TOTAL lines $(grep -h '^TOTAL' r20.*.out | wc -l)"
grep -h '^TOTAL' r20.*.out | awk '{ for (i = 1; i < NF; i++) { if ($i == "fails") f += $(i + 1); if ($i == "budget") b += $(i + 1); if ($i == "surv") s += $(i + 1); if ($i == "bs" && $(i + 1) != "-1") bs += $(i + 1) } }
  END { print "fails", f + 0, "budget", b + 0, "surv", s + 0, "bs", bs + 0 }'
grep -h '^TOTAL' r20.*.out | sed 's/.* climit /climit /' | sort | uniq -c
echo "nonempty err files $(find . -maxdepth 1 -name 'r20.*.err' -size +0 | wc -l)"
grep -h '^== shard' n20.595808_*.log | awk '{ g += $5 } END { print "shard header graphs", g }'
rm -rf "$T"
echo DONE
