#!/bin/bash
#SBATCH --job-name=l14-p18-n-bd
#SBATCH --partition=amdsmall
#SBATCH --time=00:45:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --array=0-44
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-profile18-n-boundary-%A_%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
index=$((SLURM_ARRAY_TASK_ID + 1))
python3 msi-stage/solve-l14-profile18-n0131-boundary.py \
  --carrier-start="$index" --carrier-end="$index" --trace-words
