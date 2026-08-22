#!/bin/bash
#SBATCH --job-name=leavitt-d4-five
#SBATCH --partition=agsmall
#SBATCH --array=0-127
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --time=00:30:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/research/artifacts/leavitt-d4-five-%A-%a.out

cd /projects/standard/hsiehph/sauer354/nonsofic_existence || exit 1
python3 research/artifacts/search-degree4-five-corner-omega.py \
  --shard "$SLURM_ARRAY_TASK_ID" --shards 128

