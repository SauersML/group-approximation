#!/bin/bash
#SBATCH --job-name=d4-shared-tri
#SBATCH --partition=amdsmall
#SBATCH --time=00:20:00
#SBATCH --mem=1G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-shared-tri-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/search-degree4-shared-triangle-boundary.py
