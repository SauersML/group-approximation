#!/bin/bash
#SBATCH --partition=sioux
#SBATCH --nodelist=acn112
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --time=00:10:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/atlas_integral_torsion/bockstein-%j.out

cd /projects/standard/hsiehph/sauer354/atlas_integral_torsion/run/experiments
python3 atlas_boundary_integral_bockstein.py
