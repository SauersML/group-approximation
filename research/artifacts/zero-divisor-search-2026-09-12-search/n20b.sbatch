#!/bin/bash -l
#SBATCH -J zds-n20b
#SBATCH -p agsmall
#SBATCH -t 08:00:00
#SBATCH --mem=1G
#SBATCH -c 1
#SBATCH --array=0-127%16
#SBATCH -o /scratch.global/sauer354/zds/search/n20b/n20b.%A_%a.log
# Second pass at n = 20 over the same shards and binary as n20.sbatch, with root vertex 19,
# so every graph is searched along a different tree.
cd /scratch.global/sauer354/zds/search/n20b || exit 1
OPTS="-c 1000 -cl 64000 -pw 4 8 -root 19"
i=$SLURM_ARRAY_TASK_ID
md5sum ../n20/zds20 ../n20/zds20.c "$0"
echo "== shard $i graphs $(wc -l < ../n20/g20.$i.g6) md5 $(md5sum < ../n20/g20.$i.g6 | cut -c1-32)"
t0=$(date +%s)
timeout 28000 ../n20/zds20 $OPTS < ../n20/g20.$i.g6 > r20b.$i.out 2> r20b.$i.err; rc=$?
echo "== r20b.$i opts $OPTS rc=$rc seconds=$(( $(date +%s) - t0 )) done=$(grep -c '^GRAPH' r20b.$i.out) surv=$(grep -c '^SURV' r20b.$i.out) budget=$(grep -c BUDGET r20b.$i.out)"
tail -1 r20b.$i.out; head -2 r20b.$i.err
echo ALLDONE
