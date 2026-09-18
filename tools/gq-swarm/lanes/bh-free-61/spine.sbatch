#!/bin/bash
#SBATCH -p sioux
#SBATCH -c 1
#SBATCH --mem=8G
#SBATCH --time=00:50:00
#SBATCH --job-name=bhf61-spine
#SBATCH --output=/projects/standard/hsiehph/sauer354/bhf61/%j.out
cd /projects/standard/hsiehph/sauer354/bhf61
python3 spine.py 11 4
