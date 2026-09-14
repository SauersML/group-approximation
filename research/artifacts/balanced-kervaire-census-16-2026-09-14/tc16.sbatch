#!/bin/bash -l
#SBATCH -J bc16-tc
#SBATCH -p agsmall
#SBATCH -t 06:00:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH --array=0-39%8
#SBATCH -o /scratch.global/sauer354/hl-balanced-census-16/logs/tc16.%A_%a.log
# Second, independent coset enumerator tc_verify.py (unchanged) on the L = 16, 17 classes.
cd /scratch.global/sauer354/hl-balanced-census-16 || exit 1
mkdir -p tc16
P=$(printf "part_%02d" "$SLURM_ARRAY_TASK_ID")
md5sum tc_verify.py chunks16/$P
rm -f tc16/$P
timeout 21000 /usr/bin/python3.12 tc_verify.py chunks16/$P tc16/$P 200000
echo "lines: $(wc -l < tc16/$P) / $(wc -l < chunks16/$P)"
awk '{ print $4 }' tc16/$P | sort | uniq -c
echo DONE
