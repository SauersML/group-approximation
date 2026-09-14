#!/bin/bash
#SBATCH --job-name=kprof-census
#SBATCH --time=12:00:00
#SBATCH --mem=16G
#SBATCH --cpus-per-task=1
#SBATCH --output=/scratch.global/sauer354/hl-f-kernel-profiles/logs/census_%A_%a.log
# Full F_2 census of Guba's P_(2,2) with kprof.c: all 130305 pairs, degrees 0..KMAX, 16 shards by a % 16.
set -u
cd /scratch.global/sauer354/hl-f-kernel-profiles
md5sum kprof.c census_shard.sh
KMAX=${KMAX:-10}
bash census_shard.sh $SLURM_ARRAY_TASK_ID 16 $KMAX
echo "EXIT $? $(date)"
