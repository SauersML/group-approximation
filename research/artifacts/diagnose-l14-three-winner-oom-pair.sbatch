#!/bin/bash
#SBATCH --job-name=d4-three-oom-pair
#SBATCH --partition=agsmall
#SBATCH --array=0-1
#SBATCH --time=02:00:00
#SBATCH --mem=16G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-three-oom%a-%A.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence

if (( SLURM_ARRAY_TASK_ID == 0 )); then
  carrier=293
  target=2
  rotation=12
else
  carrier=313
  target=3
  rotation=4
fi

python3 msi-stage/solve-l14-three-winner-boundary.py \
  --carrier-index "$carrier" --target "$target" \
  --rotation-index "$rotation"
