#!/bin/bash
#SBATCH --job-name=atlas-bat1
#SBATCH --partition=amdsmall
#SBATCH --time=04:00:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/atlas-rank5-balanced-area-%j.log

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
module load python3/3.12.4_anaconda2024.06-1_libmamba
python3 experiments/atlas_three_mode_balanced_area.py \
  --state-cap 500000 --stop-gcd-one \
  --emit experiments/atlas-rank5-balanced-area.json
echo SENTINEL_ATLAS_BAT1_DONE
