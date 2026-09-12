#!/bin/bash
#SBATCH --job-name=d4-l14-p27
#SBATCH --partition=amdsmall
#SBATCH --time=00:30:00
#SBATCH --mem=2G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-profile-27-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/rank-degree4-length12-triangles.py \
  --length=14 --profile=---+++--++++++ --balanced-only \
  --show-rank=9 --classify-rank=9
