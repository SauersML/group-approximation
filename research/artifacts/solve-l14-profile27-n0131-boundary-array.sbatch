#!/bin/bash
#SBATCH --job-name=l14-p27-n131r
#SBATCH --partition=amdsmall
#SBATCH --time=00:20:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --array=0-66
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-profile27-n0131r-%A_%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/solve-l14-profile27-n0131-boundary.py \
  --carrier-start=1 --carrier-end=1 \
  --rotation-start="$SLURM_ARRAY_TASK_ID" \
  --rotation-end="$SLURM_ARRAY_TASK_ID" --trace-words
