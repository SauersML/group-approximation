#!/bin/bash
#SBATCH --job-name=d4-l12-r7a
#SBATCH --partition=amdsmall
#SBATCH --array=0-11
#SBATCH --time=00:20:00
#SBATCH --mem=1G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-l12-r7a-%A-%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/search-degree4-length12-rank7-branch-a.py \
  --shard "$SLURM_ARRAY_TASK_ID"
