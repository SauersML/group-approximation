#!/bin/bash -l
#SBATCH -J zds-n22
#SBATCH -p agsmall
#SBATCH -t 08:00:00
#SBATCH --mem=1G
#SBATCH -c 1
#SBATCH --array=0-511%16
#SBATCH -o /scratch.global/sauer354/zds/search/n22/n22.%A_%a.log
#SBATCH --dependency=afterany:603674
# zds on the connected triangle-free cubic graphs with 22 vertices: shard i of 512 by geng res/mod.
# zds22 and zds22.c are copies of zds20 and zds20.c from n20/; every shard prints their md5.
SIF=/common/software/install/bundle/images/registry.msi.umn.edu/shpc_module_library/sagemath/10.7/registry.msi.umn.edu-shpc_module_library-sagemath-10.7-sha256:ea6b3bd2762c322e36841aaffe64ecad83d8969a2576d2b5165f79af3bbcdd17.sif
module load singularity 2>/dev/null
cd /scratch.global/sauer354/zds/search/n22 || exit 1
OPTS="-c 1000 -cl 64000 -pw 4 8"
i=$SLURM_ARRAY_TASK_ID
md5sum zds22 zds22.c "$0"
singularity exec -B /common,/scratch.global "$SIF" nauty-geng -c -t -d3 -D3 22 33:33 $i/512 g22.$i.g6 2> g22.$i.geng.txt
echo "== shard $i graphs $(wc -l < g22.$i.g6) md5 $(md5sum < g22.$i.g6 | cut -c1-32)"; tail -1 g22.$i.geng.txt
t0=$(date +%s)
timeout 28000 ./zds22 $OPTS < g22.$i.g6 > r22.$i.out 2> r22.$i.err; rc=$?
echo "== r22.$i opts $OPTS rc=$rc seconds=$(( $(date +%s) - t0 )) done=$(grep -c '^GRAPH' r22.$i.out) surv=$(grep -c '^SURV' r22.$i.out) budget=$(grep -c BUDGET r22.$i.out)"
tail -1 r22.$i.out; head -2 r22.$i.err
echo ALLDONE
