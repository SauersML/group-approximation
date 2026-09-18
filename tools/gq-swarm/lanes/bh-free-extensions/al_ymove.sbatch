#!/bin/bash
#SBATCH --job-name=bhfe_al_ymove
#SBATCH --partition=msismall
#SBATCH --account=hsiehph
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4g
#SBATCH --time=00:45:00
#SBATCH --output=/scratch.global/sauer354/bhfe/torsion/al_ymove_%j.out
set -uo pipefail
cd /scratch.global/sauer354/bhfe/torsion
echo "node $(hostname) $(date) python $(python3 --version 2>&1)"
md5sum al_ymove.py
python3 al_ymove.py 2400
echo "exit $?"
