#!/bin/bash
#SBATCH --job-name=leavitt-repeat-L
#SBATCH --partition=amdsmall
#SBATCH --array=0-15
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:30:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/research/artifacts/leavitt-repeat-L-%A-%a.out

cd /projects/standard/hsiehph/sauer354/nonsofic_existence || exit 1
python3 research/artifacts/search-leavitt-repeated-long-corner-radius2.py \
  --shard "$SLURM_ARRAY_TASK_ID" --shards 16
