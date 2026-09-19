#!/bin/bash
#SBATCH -p sioux
#SBATCH -c 1
#SBATCH --mem=24G
#SBATCH --time=00:55:00
#SBATCH --job-name=bhf61-spine14
#SBATCH --output=/projects/standard/hsiehph/sauer354/bhf61/%j.out
cd /projects/standard/hsiehph/sauer354/bhf61
python3 spine.py 14 4 1500000
