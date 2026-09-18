#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=8G
#SBATCH --time=00:40:00
#SBATCH --job-name=bhg2labbe-j2
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-g2-labbe/j2probe-%j.out
cd /projects/standard/hsiehph/sauer354/bh-g2-labbe
export OPENBLAS_NUM_THREADS=1
python3 -m py_compile j2probe.py || exit 3
timeout 2350 python3 j2probe.py
echo "exit=$?"
