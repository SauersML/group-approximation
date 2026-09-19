#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 4
#SBATCH --mem=8G
#SBATCH --time=00:30:00
#SBATCH --job-name=bhf18-sat
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-18/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-18
P=/usr/bin/python3.11
echo "== planted (must be UNSAT at once)"; $P bh_sat.py planted 4 60
echo "== orbit calibration (hierarchical tapes, default fill last: must be SAT)"; $P bh_sat.py orbit 4 150
echo "== full criterion"; $P bh_sat.py full 4 1380
