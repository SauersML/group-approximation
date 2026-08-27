#!/bin/bash
#SBATCH --job-name=d4-i1412-xeq1
#SBATCH --partition=amdsmall
#SBATCH --time=00:10:00
#SBATCH --mem=2G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/cairn-short-jobs/i1412-transformed-eq1-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 msi-stage/audit-l14-i1412-transformed-eq1-maximal.py

