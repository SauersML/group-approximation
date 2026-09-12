#!/bin/bash
#SBATCH --job-name=l14-p18-i-max
#SBATCH --partition=amdsmall
#SBATCH --time=00:30:00
#SBATCH --mem=4G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-profile18-i-max-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/solve-l14-profile18-i0131-maximal.py both
