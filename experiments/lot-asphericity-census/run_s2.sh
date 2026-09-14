#!/bin/bash
#SBATCH --job-name=lots2
#SBATCH --partition=msismall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=02:00:00
#SBATCH --output=/scratch.global/sauer354/hl-whitehead-lot-certify/out57/slurm-s2-%j.out
module load python/3.10.10-gcc-8.2.0-boc3bal
cd /scratch.global/sauer354/hl-whitehead-lot-certify
python3 survivors2.py 'out57/n7_*_survivors.jsonl' out57/survivors2_n7.jsonl > out57/survivors2_n7.txt 2>&1
echo DONE > out57/DONE_S2
