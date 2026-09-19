#!/bin/bash
#SBATCH --job-name=d3-k1-repeat
#SBATCH --partition=amdsmall
#SBATCH --array=0-47
#SBATCH --time=04:00:00
#SBATCH --mem=2G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d3-k1-repeat-%A-%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
branch=$((SLURM_ARRAY_TASK_ID / 12 + 1))
shard=$((SLURM_ARRAY_TASK_ID % 12))
python3 research/artifacts/search-degree3-five-seven-k1-repeated.py \
  --branch "$branch" --shard "$shard"
