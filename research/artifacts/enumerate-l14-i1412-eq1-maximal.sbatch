#!/bin/bash
#SBATCH --job-name=d4-i1412-eq1
#SBATCH --partition=amdsmall
#SBATCH --time=00:20:00
#SBATCH --mem=2G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-i1412-eq1-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/enumerate-l14-i1412-eq1-maximal.py
