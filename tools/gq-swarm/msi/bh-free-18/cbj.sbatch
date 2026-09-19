#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=4G
#SBATCH --time=00:20:00
#SBATCH --job-name=bhf18-cbj
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-free-18/%j.out
cd /projects/standard/hsiehph/sauer354/bh-free-18
/usr/bin/python3.11 bh_cbj.py
