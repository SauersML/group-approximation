#!/bin/bash
#SBATCH --job-name=d4-3carrier
#SBATCH --partition=amdsmall
#SBATCH --array=0-24
#SBATCH --time=02:00:00
#SBATCH --mem=2G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-3carrier-%A-%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/search-degree4-three-carrier-direct-collapse.py \
  --shard "$SLURM_ARRAY_TASK_ID"
