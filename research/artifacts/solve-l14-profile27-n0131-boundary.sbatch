#!/bin/bash
#SBATCH --job-name=l14-p27-n131
#SBATCH --partition=amdsmall
#SBATCH --time=00:45:00
#SBATCH --mem=10G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-profile27-n0131-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/solve-l14-profile27-n0131-boundary.py \
  --carrier-start=1 --carrier-end=1 --trace-words
