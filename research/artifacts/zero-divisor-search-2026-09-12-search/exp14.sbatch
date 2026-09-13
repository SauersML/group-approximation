#!/bin/bash -l
#SBATCH -J zds-exp14
#SBATCH -p agsmall
#SBATCH -t 01:30:00
#SBATCH --mem=4G
#SBATCH -c 4
#SBATCH -o /scratch.global/sauer354/zds/search/exp14.%j.log
# zds v3 at n = 14: regression against v2, then root probes, inner power and BS sieves, BFS order,
# and inner coset limits. Four slots run in parallel.
cd /scratch.global/sauer354/zds/search || exit 1
cp /projects/standard/hsiehph/sauer354/zds-search/zds3.c zds3.c || exit 1
gcc -O2 -std=gnu99 -Wall -o zds3 zds3.c || { echo "compile failed"; exit 1; }
md5sum zds3.c exp14.sbatch g14.g6 testdata.txt
run() {
  name=$1; shift; t0=$(date +%s)
  ./zds3 "$@" > $name.out 2> $name.err; rc=$?
  { echo "== $name: zds3 $* rc=$rc seconds=$(( $(date +%s) - t0 )) bad=$(grep -c -E '^(FAIL|CONTROL)' $name.out) surv=$(grep -c '^SURV' $name.out)"
    tail -1 $name.out; head -2 $name.err; } > $name.sum
}
B="-c 4000 -cl 64000 -pw 4 8"
( run v3-t-c0 -t -c 0 < testdata.txt; run v3-t-c4000 -t -c 4000 -cl 64000 < testdata.txt
  run v3-ctl -t2 -c 4000 -cl 64000 < testdata.txt; run v3-bfs $B -bfs < g14.g6 ) &
( run v3-base $B < g14.g6; run v3-pwd3 $B -pwd 3 < g14.g6 ) &
( run v3-probe6 $B -probe 6 < g14.g6; run v3-probe9 $B -probe 9 < g14.g6 ) &
( run v3-bs8 $B -bs 8 -bsd 3 < g14.g6; run v3-c1000 -c 1000 -cl 64000 -pw 4 8 < g14.g6
  run v3-c16000 -c 16000 -cl 64000 -pw 4 8 < g14.g6 ) &
wait
for s in v3-t-c0 v3-t-c4000 v3-ctl v3-base v3-bfs v3-pwd3 v3-probe6 v3-probe9 v3-bs8 v3-c1000 v3-c16000; do cat $s.sum; done
for s in v3-base v3-bfs v3-probe6 v3-probe9; do
  grep '^GRAPH' $s.out | awk '{ print $5, $11 }' | sort -n |
    awk -v s=$s '{ a[NR] = $1; t += $1; p += $2 } END { print s, "graphs", NR, "nodes", t, "probe", p, "median", a[int(NR / 2)], "max", a[NR] }'
done
cmp <(grep '^GRAPH' v2-s14.out | awk '{ print $3, $5, $7 }') <(grep '^GRAPH' v3-base.out | awk '{ print $3, $5, $7 }') && echo "v3-base matches v2 per graph"
grep -h '^SURV' v3-*.out | cut -c1-200 | head -20
echo ALLDONE
