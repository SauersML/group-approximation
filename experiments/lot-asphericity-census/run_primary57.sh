#!/bin/bash
#SBATCH --job-name=lotp57
#SBATCH --partition=msismall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=6G
#SBATCH --time=08:00:00
#SBATCH --output=/scratch.global/sauer354/hl-whitehead-lot-certify/outp57/slurm-%j.out
module load python/3.10.10-gcc-8.2.0-boc3bal
cd /scratch.global/sauer354/hl-whitehead-lot-certify
for n in 5 6 7; do
  ns=$(python3 census.py $n -1 x | wc -l)
  for ((s=0; s<ns; s++)); do python3 census_primary.py $n $s outp57 || echo "FAIL n=$n s=$s" >> outp57/errors.txt; done
done
echo DONE > outp57/DONE
