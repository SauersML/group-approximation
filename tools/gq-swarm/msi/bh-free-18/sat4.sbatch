#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 4
#SBATCH --mem=8G
#SBATCH --time=00:30:00
#SBATCH --job-name=bhf18-sat4
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-18/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-18
P=/usr/bin/python3.11
echo "== harvest the 3-letter clauses (repeats job 1327013's full run without its spot-check)"; $P bh_sat_h.py full 4 300
echo "== 4-letter planted (must be UNSAT at once)"; $P bh4_sat.py planted 4 60
echo "== 4-letter orbit calibration (must be SAT)"; $P bh4_sat.py orbit 4 60
echo "== 4-letter full criterion, seeded"; $P bh4_sat.py full 4 1150
