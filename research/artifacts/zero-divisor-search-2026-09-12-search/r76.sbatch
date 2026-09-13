#!/bin/bash -l
#SBATCH -J zds-n22r76
#SBATCH -p agsmall
#SBATCH -t 06:00:00
#SBATCH --mem=1G
#SBATCH -c 1
#SBATCH --array=0-3%4
#SBATCH -o /scratch.global/sauer354/zds/search/n22r76/r76.%A_%a.log
# Shard 76 of the n = 22 run (job 603988) hit its 28000 s timeout after 3106 of 4046 graphs.
# This reruns graphs 3107..4046 of g22.76.g6 in 4 chunks of 235 with the same binary and
# sieve 6 exponent bound 12. It reads ../n22 and writes only in n22r76.
cd /scratch.global/sauer354/zds/search/n22r76 || exit 1
B=../n22/zds22
[ "$(md5sum < ../n22/zds22.c | cut -c1-32)" = 18a83240ff82d0bcdcdcd33c15780d72 ] || { echo "zds source md5 mismatch"; exit 1; }
md5sum $B ../n22/zds22.c ../n22/g22.76.g6 "$0"
i=$SLURM_ARRAY_TASK_ID
lo=$((3107 + 235*i)); hi=$((lo + 234))
sed -n "${lo},${hi}p" ../n22/g22.76.g6 > g22.76.part$i.g6
echo "== part $i lines $lo-$hi graphs $(wc -l < g22.76.part$i.g6) md5 $(md5sum < g22.76.part$i.g6 | cut -c1-32)"
OPTS="-c 1000 -cl 64000 -pw 4 12"
t0=$(date +%s)
timeout 20000 $B $OPTS < g22.76.part$i.g6 > r76.part$i.out 2> r76.part$i.err; rc=$?
echo "== r76.part$i opts $OPTS rc=$rc seconds=$(( $(date +%s) - t0 )) done=$(grep -c '^GRAPH' r76.part$i.out) surv=$(grep -c '^SURV' r76.part$i.out) budget=$(grep -c BUDGET r76.part$i.out)"
tail -1 r76.part$i.out; head -2 r76.part$i.err
echo ALLDONE
