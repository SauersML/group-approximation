#!/bin/bash
#SBATCH --job-name=leavitt-d3-carrier
#SBATCH --partition=agsmall
#SBATCH --array=0-12
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --time=00:15:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/research/artifacts/leavitt-d3-carrier-%A-%a.out

cd /projects/standard/hsiehph/sauer354/nonsofic_existence || exit 1
python3 research/artifacts/search-degree3-repeated-carrier-transport.py \
  --shard "$SLURM_ARRAY_TASK_ID" --shards 13
