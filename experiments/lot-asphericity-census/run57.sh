#!/bin/bash
#SBATCH --job-name=lot57
#SBATCH --partition=msismall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=04:00:00
#SBATCH --output=/scratch.global/sauer354/hl-whitehead-lot-certify/out57/slurm-%j.out
module load python/3.10.10-gcc-8.2.0-boc3bal
cd /scratch.global/sauer354/hl-whitehead-lot-certify
python3 controls.py > out57/controls.txt 2>&1
grep -q 'CONTROLS ALL_PASS' out57/controls.txt || { echo CONTROLS_FAILED > out57/DONE; exit 2; }
for n in 5 6 7; do
  ns=$(python3 census.py $n -1 x | wc -l)
  for ((s=0; s<ns; s++)); do python3 census.py $n $s out57 || echo "FAIL n=$n s=$s" >> out57/errors.txt; done
done
echo DONE57 > out57/DONE
