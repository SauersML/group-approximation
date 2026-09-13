#!/bin/bash -l
#SBATCH -J zds-n20
#SBATCH -p agsmall
#SBATCH -t 08:00:00
#SBATCH --mem=1G
#SBATCH -c 1
#SBATCH --array=0-127%16
#SBATCH -o /scratch.global/sauer354/zds/search/n20/n20.%A_%a.log
# zds on the connected triangle-free cubic graphs with 20 vertices: shard i of 128 by geng res/mod.
# The binary zds20 is compiled once from zds3.c before submission; every shard prints its md5.
SIF=/common/software/install/bundle/images/registry.msi.umn.edu/shpc_module_library/sagemath/10.7/registry.msi.umn.edu-shpc_module_library-sagemath-10.7-sha256:ea6b3bd2762c322e36841aaffe64ecad83d8969a2576d2b5165f79af3bbcdd17.sif
module load singularity 2>/dev/null
cd /scratch.global/sauer354/zds/search/n20 || exit 1
OPTS="-c 1000 -cl 64000 -pw 4 8"
i=$SLURM_ARRAY_TASK_ID
md5sum zds20 zds20.c "$0"
singularity exec -B /common,/scratch.global "$SIF" nauty-geng -c -t -d3 -D3 20 30:30 $i/128 g20.$i.g6 2> g20.$i.geng.txt
echo "== shard $i graphs $(wc -l < g20.$i.g6) md5 $(md5sum < g20.$i.g6 | cut -c1-32)"; tail -1 g20.$i.geng.txt
t0=$(date +%s)
timeout 28000 ./zds20 $OPTS < g20.$i.g6 > r20.$i.out 2> r20.$i.err; rc=$?
echo "== r20.$i opts $OPTS rc=$rc seconds=$(( $(date +%s) - t0 )) done=$(grep -c '^GRAPH' r20.$i.out) surv=$(grep -c '^SURV' r20.$i.out) budget=$(grep -c BUDGET r20.$i.out)"
tail -1 r20.$i.out; head -2 r20.$i.err
echo ALLDONE
