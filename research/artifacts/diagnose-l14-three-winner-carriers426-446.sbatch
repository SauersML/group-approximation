#!/bin/bash
#SBATCH --job-name=d4-three-c426-446
#SBATCH --partition=agsmall
#SBATCH --time=02:00:00
#SBATCH --mem=32G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-three-c426-446-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/solve-l14-three-winner-boundary.py --carrier-start 426 --carrier-end 446
