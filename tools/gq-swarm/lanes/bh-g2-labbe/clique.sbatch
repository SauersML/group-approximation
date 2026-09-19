#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=12G
#SBATCH --time=00:30:00
#SBATCH --job-name=bhg2labbe-clique
#SBATCH --output=/projects/standard/hsiehph/sauer354/bh-g2-labbe/clique-%j.out
cd /projects/standard/hsiehph/sauer354/bh-g2-labbe
timeout 1740 python3 cliquectx.py
echo "exit=$?"
