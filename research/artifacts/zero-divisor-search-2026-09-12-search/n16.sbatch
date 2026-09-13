#!/bin/bash -l
#SBATCH -J zds-n16
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=4G
#SBATCH -c 4
#SBATCH -o /scratch.global/sauer354/zds/search/n16.%j.log
# zds v2 on every connected triangle-free cubic graph with n = 6..16 vertices (n = 16 in 4 shards).
SIF=/common/software/install/bundle/images/registry.msi.umn.edu/shpc_module_library/sagemath/10.7/registry.msi.umn.edu-shpc_module_library-sagemath-10.7-sha256:ea6b3bd2762c322e36841aaffe64ecad83d8969a2576d2b5165f79af3bbcdd17.sif
module load singularity 2>/dev/null
cd /scratch.global/sauer354/zds/search || exit 1
cp /projects/standard/hsiehph/sauer354/zds-search/zds.c zds.c || exit 1
gcc -O2 -std=gnu99 -Wall -o zds2 zds.c || { echo "compile failed"; exit 1; }
md5sum zds.c n16.sbatch
OPTS="-c 4000 -cl 64000 -pw 4 8"
for n in 6 8 10 12 14 16; do
  singularity exec -B /common,/scratch.global "$SIF" nauty-geng -c -t -d3 -D3 $n g$n.g6 2> g$n.geng.txt
  echo "== n=$n graphs $(wc -l < g$n.g6) md5 $(md5sum < g$n.g6 | cut -c1-32)"; tail -1 g$n.geng.txt
done
for n in 6 8 10 12 14; do
  t0=$(date +%s)
  ./zds2 $OPTS < g$n.g6 > r$n.out 2> r$n.err; rc=$?
  echo "== r$n rc=$rc seconds=$(( $(date +%s) - t0 )) surv=$(grep -c '^SURV' r$n.out)"; tail -1 r$n.out; head -2 r$n.err
done
awk '{ print > ("g16." (NR % 4) ".g6") }' g16.g6
t0=$(date +%s)
for i in 0 1 2 3; do
  ( timeout 13500 ./zds2 $OPTS < g16.$i.g6 > r16.$i.out 2> r16.$i.err; echo "rc=$?" > r16.$i.rc ) &
done
wait
for i in 0 1 2 3; do
  echo "== r16.$i graphs $(wc -l < g16.$i.g6) $(cat r16.$i.rc) done=$(grep -c '^GRAPH' r16.$i.out) surv=$(grep -c '^SURV' r16.$i.out)"
  tail -1 r16.$i.out; head -2 r16.$i.err
done
echo "== n=16 seconds=$(( $(date +%s) - t0 ))"
cat r16.0.out r16.1.out r16.2.out r16.3.out | grep '^GRAPH' | awk '{ print $5 }' | sort -n |
  awk '{ a[NR] = $1; s += $1 } END { print "graphs", NR, "nodes", s, "median", a[int(NR / 2)], "p90", a[int(NR * 0.9)], "max", a[NR] }'
grep -h '^SURV' r16.*.out | cut -c1-200
echo ALLDONE
