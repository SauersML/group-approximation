#!/bin/bash
#SBATCH --job-name=d3-l11-repeat
#SBATCH --partition=amdsmall
#SBATCH --array=0-47
#SBATCH --time=02:00:00
#SBATCH --mem=2G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d3-l11-repeat-%A-%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
mode=$((SLURM_ARRAY_TASK_ID / 12))
shard=$((SLURM_ARRAY_TASK_ID % 12))
python3 research/artifacts/search-degree3-five-five-repeated.py \
  --mode "$mode" --shard "$shard"
