#!/bin/bash -l
#SBATCH -J bc16-prep
#SBATCH -p agsmall
#SBATCH -t 02:00:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-balanced-census-16/logs/prep16.%j.log
# After the census job: split the L = 16, 17 classes into 40 round-robin chunks, then run the
# orbit-counting recount of the whole L <= 17 census.
cd /scratch.global/sauer354/hl-balanced-census-16 || exit 1
md5sum census17.txt census_L16.txt census_L17.txt rc_orbit.py
cat census_L16.txt census_L17.txt > census_L1617.txt
echo "classes L=16,17: $(wc -l < census_L1617.txt)"
rm -rf chunks16 && mkdir chunks16
awk '{ f = sprintf("chunks16/part_%02d", (NR - 1) % 40); print > f }' census_L1617.txt
echo "lines in chunks: $(cat chunks16/part_* | wc -l)"
md5sum census_L1617.txt
/usr/bin/python3.12 rc_orbit.py census17.txt 2 17 > rc17.txt
awk '/^block/ && $2 + $3 >= 16' rc17.txt
grep -c " BAD" rc17.txt
tail -n 3 rc17.txt
md5sum rc17.txt
echo DONE
