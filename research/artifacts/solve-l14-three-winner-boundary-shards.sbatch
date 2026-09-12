#!/bin/bash
#SBATCH --job-name=d4-three-shards
#SBATCH --partition=agsmall
#SBATCH --array=0-40
#SBATCH --time=02:00:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-three-shard%a-%A.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence

if (( SLURM_ARRAY_TASK_ID < 28 )); then
  start=$((SLURM_ARRAY_TASK_ID * 10 + 1))
  end=$((start + 9))
  (( end > 275 )) && end=275
else
  offset=$((SLURM_ARRAY_TASK_ID - 28))
  start=$((301 + offset * 10))
  end=$((start + 9))
  (( end > 425 )) && end=425
fi

python3 msi-stage/solve-l14-three-winner-boundary.py \
  --carrier-start "$start" --carrier-end "$end"
