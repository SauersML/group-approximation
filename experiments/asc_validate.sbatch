#!/bin/bash
#SBATCH --job-name=asc-validate
#SBATCH --partition=a100-4
#SBATCH --gres=gpu:a100:1
#SBATCH --time=00:40:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/asc-validate.out
set -euo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
PY=/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3
nvidia-smi --query-gpu=name,memory.total --format=csv,noheader

echo "== gate: U = I baseline (boundary must vanish, interior must not) =="
$PY experiments/atlas_asc_covariance_gpu.py --init identity --iterations 0 \
    --eval-probes 512 --mode descend

echo "== timing: 40 escape steps =="
$PY experiments/atlas_asc_covariance_gpu.py --init perturbed --iterations 40 \
    --report-every 10 --eval-every 40 --probes 32 --word-batch 24
echo SENTINEL_VALIDATE_DONE
