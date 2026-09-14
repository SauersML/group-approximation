#!/bin/bash -l
#SBATCH -J mgb-census16
#SBATCH -p agsmall
#SBATCH -t 08:00:00
#SBATCH --mem=4G
#SBATCH -c 3
#SBATCH -o /scratch.global/sauer354/magnus-builder/census16.%j.log
# Lane solve-magnus-graph-builder: regenerate the L=16 uncertified residue lists.
cd /scratch.global/sauer354/magnus-builder || exit 1
PY=/usr/bin/python3.12
md5sum census.py census2.py census3.py malnormal.py "$0"
( timeout 25000 $PY census.py 16 16 100000 > census_seq16.out 2>&1; echo "census rc=$?" ) &
( timeout 25000 $PY malnormal.py 16 100000 > malnormal16.out 2>&1; echo "malnormal rc=$?" ) &
( timeout 28000 $PY census3.py 16 16 100000 > census3_16.out 2>&1; echo "census3 rc=$?" ) &
wait
tail -3 census_seq16.out malnormal16.out census3_16.out
echo ALLDONE
