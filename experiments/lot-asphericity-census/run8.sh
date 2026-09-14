#!/bin/bash
#SBATCH --job-name=lot8
#SBATCH --partition=msismall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --time=12:00:00
#SBATCH --output=/scratch.global/sauer354/hl-whitehead-lot-certify/out8/slurm-%A_%a.out
# submit with: sbatch --array=<comma list of diam>=4 shape indices>%8 run8.sh
module load python/3.10.10-gcc-8.2.0-boc3bal
cd /scratch.global/sauer354/hl-whitehead-lot-certify
python3 census.py 8 "$SLURM_ARRAY_TASK_ID" out8 || echo "FAIL s=$SLURM_ARRAY_TASK_ID" >> out8/errors.txt
