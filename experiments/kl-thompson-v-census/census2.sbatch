#!/bin/bash -l
#SBATCH -J hlkl-census
#SBATCH -p agsmall
#SBATCH -t 01:00:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-kl-counterexample/census2.%j.log
cd /scratch.global/sauer354/hl-kl-counterexample || exit 1
md5sum census2.py
/usr/bin/python3.12 census2.py 6,7 survivors67.txt
wc -l survivors67.txt
mkdir -p chunks results
rm -f chunks/part_* results/part_*
split -d -a 3 -n l/40 survivors67.txt chunks/part_
ls chunks | wc -l
echo DONE
