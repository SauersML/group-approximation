#!/bin/bash
#SBATCH -p sioux
#SBATCH -c 1
#SBATCH --mem=8G
#SBATCH --time=00:50:00
#SBATCH --job-name=bhf61-clos3
#SBATCH --output=/projects/standard/hsiehph/sauer354/bhf61/%j.out
cd /projects/standard/hsiehph/sauer354/bhf61
python3 closure_n.py 3 24 10 300000
