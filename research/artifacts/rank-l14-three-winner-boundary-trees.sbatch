#!/bin/bash
#SBATCH --job-name=l14-3win-nc
#SBATCH --time=00:30:00
#SBATCH --mem=4G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-3win-nc-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/rank-l14-three-winner-boundary-trees.py
