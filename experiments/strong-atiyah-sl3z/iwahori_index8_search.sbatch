#!/bin/bash
#SBATCH --job-name=satk-iwahori8
#SBATCH --time=03:00:00
#SBATCH --mem=32G
#SBATCH --cpus-per-task=1
#SBATCH --output=/scratch.global/sauer354/satk-gap/iwahori_index8_search.%j.log

# Search for a torsion-free index-8 subgroup of the pro-2 Iwahori of SL_3(Z_2), mod 16.
# usage: sbatch iwahori_index8_search.sbatch   (script copied to /scratch.global/sauer354/satk-gap/)
set -uo pipefail
module load sagemath/10.7
export DOT_SAGE=/scratch.global/sauer354/satk-gap/.sage
cd /scratch.global/sauer354/satk-gap
echo "stage=start $(date)"
echo 'Read("iwahori_index8_search.g");' | sage -gap -q -o 30g
echo "stage=done rc=$? $(date)"
