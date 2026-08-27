#!/bin/bash
#SBATCH --job-name=d4-latin
#SBATCH --partition=amdsmall
#SBATCH --time=00:20:00
#SBATCH --mem=1G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-latin-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/search-degree4-latin-triangle-boundary.py
