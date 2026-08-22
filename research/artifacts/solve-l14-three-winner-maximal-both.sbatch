#!/bin/bash
#SBATCH --job-name=d4-three-max-both
#SBATCH --partition=amdsmall
#SBATCH --time=04:00:00
#SBATCH --mem=64G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-three-max-both-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/solve-l14-three-winner-maximal-states.py both
