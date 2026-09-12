#!/bin/bash
#SBATCH --job-name=l14-p27-n131t
#SBATCH --partition=amdsmall
#SBATCH --time=00:15:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --array=0-267
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-profile27-n0131t-%A_%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
rotation=$((SLURM_ARRAY_TASK_ID / 4))
target=$((SLURM_ARRAY_TASK_ID % 4))
python3 msi-stage/solve-l14-profile27-n0131-boundary.py \
  --carrier-start=1 --carrier-end=1 \
  --rotation-start="$rotation" --rotation-end="$rotation" \
  --target-start="$target" --target-end="$target" --trace-words
