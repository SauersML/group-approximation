#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 16
#SBATCH --mem=16G
#SBATCH --time=00:25:00
#SBATCH --job-name=bhf18-lazy
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-18/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-18
/usr/bin/python3.11 bh_lazy_par.py 16 3 4000
