#!/bin/bash -l
#SBATCH -J bc16-census
#SBATCH -p agsmall
#SBATCH -t 03:00:00
#SBATCH --mem=32G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-balanced-census-16/logs/census17.%j.log
cd /scratch.global/sauer354/hl-balanced-census-16 || exit 1
md5sum census_balanced.py census15.txt
/usr/bin/python3.12 census_balanced.py 17 census17.txt 2> census17.stats
cat census17.stats
wc -l < census17.txt
echo "prefix15 md5: $(head -n 24571 census17.txt | md5sum)"
awk "\$2==16" census17.txt > census_L16.txt
awk "\$2==17" census17.txt > census_L17.txt
wc -l census_L16.txt census_L17.txt
md5sum census17.txt census_L16.txt census_L17.txt
echo DONE
