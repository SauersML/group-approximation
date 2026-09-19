#!/bin/bash
#SBATCH --job-name=l14-p27-n131r
#SBATCH --partition=amdsmall
#SBATCH --time=01:00:00
#SBATCH --mem=12G
#SBATCH --cpus-per-task=1
#SBATCH --array=0-8575%199
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-profile27-n0131r-%A_%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
prefixes=32
per_rotation=$((4 * prefixes))
rotation=$((SLURM_ARRAY_TASK_ID / per_rotation))
within=$((SLURM_ARRAY_TASK_ID % per_rotation))
target=$((within / prefixes))
prefix=$((within % prefixes))
python3 msi-stage/solve-l14-profile27-131-qblock.py n0131 \
  --rotation="$rotation" --target="$target" \
  --prefix="$prefix" --prefix-bits=5
