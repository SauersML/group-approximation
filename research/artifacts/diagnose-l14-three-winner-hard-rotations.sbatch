#!/bin/bash
#SBATCH --job-name=d4-three-hard-rotation
#SBATCH --partition=agsmall
#SBATCH --array=0-491
#SBATCH --time=00:30:00
#SBATCH --mem=2G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-three-rot%a-%A.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence

carriers=(293 309 313)
carrier_index=$((SLURM_ARRAY_TASK_ID / 164))
remainder=$((SLURM_ARRAY_TASK_ID % 164))
target=$((remainder / 41))
rotation=$((remainder % 41))
carrier=${carriers[$carrier_index]}

python3 msi-stage/solve-l14-three-winner-boundary.py \
  --carrier-index "$carrier" --target "$target" \
  --rotation-index "$rotation"
