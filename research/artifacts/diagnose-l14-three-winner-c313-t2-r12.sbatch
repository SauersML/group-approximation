#!/bin/bash
#SBATCH --job-name=d4-three-c313-t2-r12
#SBATCH --partition=agsmall
#SBATCH --time=02:00:00
#SBATCH --mem=16G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-three-c313-t2-r12-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/solve-l14-three-winner-boundary.py \
  --carrier-index 313 --target 2 --rotation-index 12
