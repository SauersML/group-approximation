#!/bin/bash
#SBATCH --job-name=d4-r7-trees
#SBATCH --partition=amdsmall
#SBATCH --time=01:00:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-r7-trees-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/enumerate-degree4-length12-rank7-cancellation-trees.py \
  --max-equations 10 --examples 500
