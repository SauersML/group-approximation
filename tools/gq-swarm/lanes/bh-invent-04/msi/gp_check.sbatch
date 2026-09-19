#!/bin/bash
#SBATCH --job-name=bhi04-gp
#SBATCH -p ag2tb,msismall
#SBATCH -c 1
#SBATCH --mem=1G
#SBATCH --time=00:10:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-invent-04/gp-%j.out
cd /projects/standard/hsiehph/sauer354/bh-invent-04 || exit 2
PY=$(command -v python3 || true)
if [ -z "$PY" ]; then module load python3 2>/dev/null || module load python 2>/dev/null; PY=$(command -v python3); fi
echo "host=$(hostname) py=$PY"
timeout 540 "$PY" gp_check.py
echo "rc=$?"
