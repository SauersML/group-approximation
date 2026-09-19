#!/bin/bash
#SBATCH --job-name=nm-uncond-detector2
#SBATCH --partition=msismall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=6G
#SBATCH --time=00:55:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/ms-nm-uncond-a/detector2.%j.out
cd /projects/standard/hsiehph/sauer354/ms-nm-uncond-a/snap || exit 3
[ -f scripts/sentence_census.py ] || tar -xzf ../snap.tgz || exit 4
PY=$(command -v python3.11 || echo /usr/bin/python3.11)
$PY -u ../driver.py
echo "rc=$?"
