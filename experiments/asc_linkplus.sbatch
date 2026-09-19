#!/bin/bash
#SBATCH --job-name=asc-linkplus
#SBATCH --partition=msigpu,a100-4
#SBATCH --gres=gpu:1
#SBATCH --time=00:40:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/asc-linkplus.out
set -uo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
PY=/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3
$PY experiments/atlas_asc_link_probe.py --mode both --iterations 600 \
    --report-every 100 --lr 0.08 --out experiments/asc-linkplus.jsonl
echo SENTINEL_LINKPLUS_DONE
