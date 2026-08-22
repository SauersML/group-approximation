#!/bin/bash
#SBATCH --job-name=d4-latin-solved
#SBATCH --partition=amdsmall
#SBATCH --array=0-330
#SBATCH --time=01:00:00
#SBATCH --mem=1G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-latin-solved-%A-%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/search-degree4-latin-projection-solved.py \
  --a-index "$SLURM_ARRAY_TASK_ID"
