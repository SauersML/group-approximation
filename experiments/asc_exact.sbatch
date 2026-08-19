#!/bin/bash
#SBATCH --job-name=asc-exact
#SBATCH --partition=a100-4
#SBATCH --gres=gpu:a100:1
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=120g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/asc-exact.out
set -uo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
PY=/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3
$PY experiments/atlas_asc_tangent_exact.py --out experiments/asc-exact.json
echo SENTINEL_EXACT_DONE
