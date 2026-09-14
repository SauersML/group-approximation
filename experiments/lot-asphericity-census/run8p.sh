#!/bin/bash
#SBATCH --job-name=lot8p
#SBATCH --partition=msismall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=6G
#SBATCH --time=12:00:00
#SBATCH --output=/scratch.global/sauer354/hl-whitehead-lot-certify/out8p/slurm-%A_%a.out
module load python/3.10.10-gcc-8.2.0-boc3bal
cd /scratch.global/sauer354/hl-whitehead-lot-certify
python3 census8p.py 8 "$SLURM_ARRAY_TASK_ID" out8p || echo "FAIL s=$SLURM_ARRAY_TASK_ID" >> out8p/errors.txt
