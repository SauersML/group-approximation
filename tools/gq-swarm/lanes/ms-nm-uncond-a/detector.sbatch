#!/bin/bash
#SBATCH --job-name=nm-uncond-detector
#SBATCH --partition=msismall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:20:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/ms-nm-uncond-a/detector.%j.out
cd /projects/standard/hsiehph/sauer354/ms-nm-uncond-a/snap || exit 3
tar -xzf ../snap.tgz || exit 4
echo "base "
PY=$(command -v python3.11 || echo /usr/bin/python3.11)
$PY scripts/sentence_census.py --verify-unconditional > /projects/standard/hsiehph/sauer354/ms-nm-uncond-a/detector.findings.txt 2>&1
echo "rc=$?"
wc -l /projects/standard/hsiehph/sauer354/ms-nm-uncond-a/detector.findings.txt
