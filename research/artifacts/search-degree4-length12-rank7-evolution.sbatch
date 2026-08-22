#!/bin/bash
#SBATCH --job-name=d4-r7-evolve
#SBATCH --partition=amdsmall
#SBATCH --array=0-63
#SBATCH --time=01:00:00
#SBATCH --mem=2G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-r7-evolve-%A-%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/search-degree4-length12-rank7-evolution.py \
  --seed "$SLURM_ARRAY_TASK_ID" --steps 250000
