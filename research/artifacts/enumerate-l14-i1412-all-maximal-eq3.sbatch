#!/bin/bash
#SBATCH --job-name=d4-i1412-all-eq3
#SBATCH --partition=amdsmall
#SBATCH --time=02:00:00
#SBATCH --mem=32G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-i1412-all-eq3-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/enumerate-l14-i1412-all-maximal.py eq3
