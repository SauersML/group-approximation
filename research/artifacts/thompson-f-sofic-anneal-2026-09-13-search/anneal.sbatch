#!/bin/bash
#SBATCH --job-name=tf-sofic-anneal
#SBATCH --partition=agsmall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=4G
#SBATCH --time=01:30:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/tfsofic/anneal.%j.log
cd /projects/standard/hsiehph/sauer354/tfsofic || exit 1
python3 -c 'import numpy' 2>/dev/null || module load python3 2>/dev/null || module load python 2>/dev/null
python3 --version
python3 -c 'import numpy; print("numpy", numpy.__version__)' || { echo "NO_NUMPY"; exit 2; }
for n in 64 128 256 512 1024; do
  for eps in 0.25 0.5; do
    for seed in 1 2; do
      python3 anneal.py $n $eps $((400*n)) $seed
    done
  done
done
echo DONE
