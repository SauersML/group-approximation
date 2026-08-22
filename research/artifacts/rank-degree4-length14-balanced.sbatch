#!/bin/bash
#SBATCH --job-name=d4-l14-rank
#SBATCH --partition=amdsmall
#SBATCH --time=00:30:00
#SBATCH --mem=1G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-l14-rank-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
git fetch origin main
git show origin/main:research/artifacts/rank-degree4-length12-triangles.py \
  > /tmp/rank-degree4-length14-balanced-$SLURM_JOB_ID.py
python3 /tmp/rank-degree4-length14-balanced-$SLURM_JOB_ID.py \
  --length=14 --balanced-only
