#!/bin/bash
#SBATCH --job-name=leavitt-d2-pivot
#SBATCH --partition=amdsmall
#SBATCH --array=0-9
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:30:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/research/artifacts/leavitt-d2-pivot-%A-%a.out

cd /projects/standard/hsiehph/sauer354/nonsofic_existence || exit 1
python3 research/artifacts/search-leavitt-degree2-postpivot.py \
  --shard "$SLURM_ARRAY_TASK_ID" --shards 10
