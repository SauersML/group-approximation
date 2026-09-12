#!/bin/bash
#SBATCH --job-name=d4-fifteen-n0115
#SBATCH --partition=agsmall
#SBATCH --time=08:00:00
#SBATCH --mem=32G
#SBATCH --cpus-per-task=1
#SBATCH --array=0-1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-fifteen-n0115-%A_%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
branches=(I II)
python3 msi-stage/solve-l14-fifteen-n0115-boundary.py "${branches[$SLURM_ARRAY_TASK_ID]}" --trace
