#!/bin/bash
#SBATCH --job-name=l14-p27-greedy
#SBATCH --partition=amdsmall
#SBATCH --time=00:10:00
#SBATCH --mem=4G
#SBATCH --cpus-per-task=1
#SBATCH --array=0-1
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/msi-l14-profile27-greedy-%A_%a.out

set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
classes=(n0131 i0131)
python3 msi-stage/probe-l14-profile27-131-greedy.py \
  "${classes[$SLURM_ARRAY_TASK_ID]}"
