#!/bin/bash
#SBATCH --job-name=d4-three-c293-t3-r4
#SBATCH --partition=agsmall
#SBATCH --time=02:00:00
#SBATCH --mem=16G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-three-c293-t3-r4-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/solve-l14-three-winner-boundary.py \
  --carrier-index 293 --target 3 --rotation-index 4
