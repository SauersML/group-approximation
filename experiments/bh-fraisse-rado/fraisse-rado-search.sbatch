#!/bin/bash
#SBATCH --job-name=frrado
#SBATCH --partition=msismall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=02:00:00
#SBATCH --output=/scratch.global/sauer354/hl-bh-fraisse-thompson/slurm-%j.out
module load python/3.10.10-gcc-8.2.0-boc3bal
cd /scratch.global/sauer354/hl-bh-fraisse-thompson
python3 fraisse-rado-search.py 2 > k2.txt 2>&1
python3 fraisse-rado-search.py 3 > k3.txt 2>&1
python3 fraisse-rado-search.py 4 8 > k4a8.txt 2>&1
echo DONE > DONE
