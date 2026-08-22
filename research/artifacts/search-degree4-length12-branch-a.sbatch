#!/bin/bash
#SBATCH --job-name=d4l12a
#SBATCH --array=0-11
#SBATCH --time=02:00:00
#SBATCH --mem=2G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/d4l12a-%A-%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354
python3 search-degree4-length12-branch-a.py --shard "$SLURM_ARRAY_TASK_ID"

