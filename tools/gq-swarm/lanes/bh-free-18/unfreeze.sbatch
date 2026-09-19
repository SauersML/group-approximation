#!/bin/bash
#SBATCH -p ag2tb,msismall
#SBATCH -c 4
#SBATCH --mem=8G
#SBATCH --time=00:30:00
#SBATCH --job-name=bhf18-unfreeze
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-18/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-18
/usr/bin/python3.11 bh_unfreeze.py 4 420 1100
