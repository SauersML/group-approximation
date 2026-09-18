#!/bin/bash
#SBATCH -p ag2tb,msismall
#SBATCH -c 1
#SBATCH --mem=4G
#SBATCH --time=00:10:00
#SBATCH -J bhi07pairs
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-invent-07/%j.out
cd /projects/standard/hsiehph/sauer354/bh-invent-07 || exit 1
python3 -c 'import ast,sys; ast.parse(open("pairs.py").read()); print("syntax ok")'
python3 pairs.py 530 36
