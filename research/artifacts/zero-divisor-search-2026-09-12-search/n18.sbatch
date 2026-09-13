#!/bin/bash -l
#SBATCH -J zds-n18
#SBATCH -p agsmall
#SBATCH -t 12:00:00
#SBATCH --mem=2G
#SBATCH -c 1
#SBATCH --array=0-31%8
#SBATCH -o /scratch.global/sauer354/zds/search/n18/n18.%A_%a.log
# zds on the connected triangle-free cubic graphs with 18 vertices: shard i of 32 by geng res/mod.
# The binary zds18 is compiled once before submission; its md5 is printed by every shard.
SIF=/common/software/install/bundle/images/registry.msi.umn.edu/shpc_module_library/sagemath/10.7/registry.msi.umn.edu-shpc_module_library-sagemath-10.7-sha256:ea6b3bd2762c322e36841aaffe64ecad83d8969a2576d2b5165f79af3bbcdd17.sif
module load singularity 2>/dev/null
cd /scratch.global/sauer354/zds/search/n18 || exit 1
OPTS="-c 1000 -cl 64000 -pw 4 8"
i=$SLURM_ARRAY_TASK_ID
md5sum zds18 zds18.c "$0"
singularity exec -B /common,/scratch.global "$SIF" nauty-geng -c -t -d3 -D3 18 27:27 $i/32 g18.$i.g6 2> g18.$i.geng.txt
echo "== shard $i graphs $(wc -l < g18.$i.g6) md5 $(md5sum < g18.$i.g6 | cut -c1-32)"; tail -1 g18.$i.geng.txt
t0=$(date +%s)
timeout 42000 ./zds18 $OPTS < g18.$i.g6 > r18.$i.out 2> r18.$i.err; rc=$?
echo "== r18.$i opts $OPTS rc=$rc seconds=$(( $(date +%s) - t0 )) done=$(grep -c '^GRAPH' r18.$i.out) surv=$(grep -c '^SURV' r18.$i.out) budget=$(grep -c BUDGET r18.$i.out)"
tail -1 r18.$i.out; head -2 r18.$i.err
echo ALLDONE
