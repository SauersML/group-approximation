#!/bin/bash
#SBATCH --job-name=leavitt-d4-five
#SBATCH --partition=amdsmall
#SBATCH --array=0-63
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=01:00:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-five-%A-%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/search-degree4-five-corner-omega.py \
  --shard "$SLURM_ARRAY_TASK_ID" --shards 64 --support 4
