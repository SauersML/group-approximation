#!/bin/bash
#SBATCH -p ag2tb,msismall
#SBATCH -c 1
#SBATCH --mem=8G
#SBATCH --time=00:15:00
#SBATCH -J bhi07pair2
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-invent-07/%j.out
cd /projects/standard/hsiehph/sauer354/bh-invent-07 || exit 1
python3 -c 'import ast; ast.parse(open("pairs.py").read()); ast.parse(open("pairs2.py").read()); print("syntax ok")'
python3 pairs2.py 840
