#!/bin/bash
#SBATCH --job-name=asc-link
#SBATCH --partition=msigpu,a100-4
#SBATCH --gres=gpu:1
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/asc-link.out
set -uo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
PY=/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3
$PY experiments/atlas_asc_link_probe.py --mode both --iterations 400 \
    --report-every 50 --out experiments/asc-link.jsonl
echo SENTINEL_LINK_DONE
