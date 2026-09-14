#!/bin/bash
#SBATCH --job-name=frcert
#SBATCH --partition=msismall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=01:00:00
#SBATCH --output=/scratch.global/sauer354/hl-bh-fraisse-thompson/slurm-cert-%j.out
module load python/3.10.10-gcc-8.2.0-boc3bal
cd /scratch.global/sauer354/hl-bh-fraisse-thompson
python3 fraisse-rado-certs.py > certs.jsonl 2> certs.err
python3 fraisse-rado-verify.py certs.jsonl > verify.txt 2>&1
echo DONE > CERTDONE
