#!/bin/bash
#SBATCH --job-name=affine-omega-pic
#SBATCH --partition=amdsmall
#SBATCH --array=0-7
#SBATCH --cpus-per-task=1
#SBATCH --mem=3G
#SBATCH --time=01:00:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/research/artifacts/affine-omega-pic-%A-%a.out

cd /projects/standard/hsiehph/sauer354/nonsofic_existence || exit 1
python3 research/artifacts/search-leavitt-affine-omega-relative-pictures.py \
  --min-area 6 --max-area 6 --stop-on-hit \
  --shard "$SLURM_ARRAY_TASK_ID" --shards 8
