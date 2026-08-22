#!/bin/bash
#SBATCH --job-name=d4-three-c301-330
#SBATCH --partition=agsmall
#SBATCH --array=301-330
#SBATCH --time=02:00:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-three-c%a-%A.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/solve-l14-three-winner-boundary.py \
  --carrier-index "$SLURM_ARRAY_TASK_ID"
