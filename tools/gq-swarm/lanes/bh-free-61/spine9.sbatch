#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=4G
#SBATCH --time=00:20:00
#SBATCH --job-name=bhf61-spine9
#SBATCH --output=/projects/standard/hsiehph/sauer354/bhf61/%j.out
cd /projects/standard/hsiehph/sauer354/bhf61
python3 spine.py 9 3
