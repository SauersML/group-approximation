#!/bin/bash
#SBATCH --job-name=d4-three-c313-16g
#SBATCH --partition=agsmall
#SBATCH --array=0-163
#SBATCH --time=02:00:00
#SBATCH --mem=16G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-three-c313x%a-%A.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence

target=$((SLURM_ARRAY_TASK_ID / 41))
rotation=$((SLURM_ARRAY_TASK_ID % 41))
python3 msi-stage/solve-l14-three-winner-boundary.py \
  --carrier-index 313 --target "$target" --rotation-index "$rotation"
