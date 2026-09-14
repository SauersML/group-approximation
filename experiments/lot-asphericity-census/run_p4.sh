#!/bin/bash
#SBATCH --job-name=lotp4
#SBATCH --partition=msismall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=04:00:00
#SBATCH --output=/scratch.global/sauer354/hl-whitehead-lot-certify/outp57/slurm-p4-%j.out
module load python/3.10.10-gcc-8.2.0-boc3bal
cd /scratch.global/sauer354/hl-whitehead-lot-certify
python3 survivorsp4.py 'outp57/n7_*_survivors.jsonl' outp57/survivorsp4_n7.jsonl > outp57/survivorsp4_n7.txt 2>&1
echo DONE > outp57/DONE_P4
