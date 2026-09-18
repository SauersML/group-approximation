#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=8G
#SBATCH --time=00:30:00
#SBATCH --job-name=bhg2labbe-walls
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-g2-labbe/walls-%j.out
cd /projects/standard/hsiehph/sauer354/bh-g2-labbe
timeout 1700 python3 wallsearch.py
echo "exit=$?"
