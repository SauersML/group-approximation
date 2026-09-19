#!/bin/bash
#SBATCH --job-name=d4-i1412-pairs
#SBATCH --partition=amdsmall
#SBATCH --time=01:00:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-i1412-pairs-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/enumerate-l14-i1412-carrier-pairs.py
