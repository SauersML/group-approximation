#!/bin/bash
#SBATCH --job-name=leavitt-d4-five
#SBATCH --partition=agsmall
#SBATCH --array=0-63
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=02:00:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/leavitt-d4-five-%A-%a.out

cd /projects/standard/hsiehph/sauer354 || exit 1
python3 search-degree4-five-corner-omega.py \
  --shard "$SLURM_ARRAY_TASK_ID" --shards 64 --support 4
