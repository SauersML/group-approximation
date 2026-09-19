#!/bin/bash
#SBATCH --job-name=leavitt-d3-two-pivot
#SBATCH --partition=agsmall
#SBATCH --array=0-10
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:30:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/research/artifacts/leavitt-d3-two-pivot-%A-%a.out

cd /projects/standard/hsiehph/sauer354/nonsofic_existence || exit 1
for offset in $(seq 0 50000 1650000); do
  python3 research/artifacts/search-leavitt-degree3-postpivot.py \
    --shard "$SLURM_ARRAY_TASK_ID" --shards 11 \
    --offset "$offset" --limit 50000 --mode two_pivot || exit $?
done
