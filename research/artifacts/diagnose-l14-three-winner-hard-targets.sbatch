#!/bin/bash
#SBATCH --job-name=d4-three-hard-target
#SBATCH --partition=agsmall
#SBATCH --array=0-11
#SBATCH --time=02:00:00
#SBATCH --mem=4G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-three-hard%a-%A.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence

carriers=(293 309 313)
carrier=${carriers[$((SLURM_ARRAY_TASK_ID / 4))]}
target=$((SLURM_ARRAY_TASK_ID % 4))
python3 msi-stage/solve-l14-three-winner-boundary.py \
  --carrier-index "$carrier" --target "$target"
