#!/bin/bash
#SBATCH --job-name=d4-r9-split
#SBATCH --partition=amdsmall
#SBATCH --array=0-7
#SBATCH --time=00:20:00
#SBATCH --mem=4G
#SBATCH --cpus-per-task=1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-d4-r9-split-%j.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
python3 research/artifacts/split-degree4-length12-rank9-carriers.py \
  --task "$SLURM_ARRAY_TASK_ID"
