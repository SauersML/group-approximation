#!/bin/bash -l
#SBATCH -J zdsth-c6
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=2G
#SBATCH -c 1
#SBATCH -o /users/0/sauer354/zdsth/c6.%j.log
# Cycle-relator census for 6-cycles of Kaplansky graphs (support-3 zero divisors).
cd ~/zdsth || exit 1
md5sum cycle_relators.py "$0"
mkdir -p c6run && cp cycle_relators.py c6run/ && cd c6run || exit 1
/usr/bin/python3.12 cycle_relators.py 6 > c6.out 2>&1
echo "EXIT $?"
