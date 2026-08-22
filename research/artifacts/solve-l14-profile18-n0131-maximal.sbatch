#!/bin/bash
#SBATCH --job-name=l14-p18-n-max
#SBATCH --partition=amdsmall
#SBATCH --time=00:45:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-profile18-n-max-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/solve-l14-profile18-n0131-maximal.py both
