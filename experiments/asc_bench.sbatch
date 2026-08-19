#!/bin/bash
#SBATCH --job-name=asc-bench
#SBATCH --partition=a100-4
#SBATCH --gres=gpu:a100:1
#SBATCH --time=00:25:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/asc-bench.out
set -uo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
PY=/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3
nvidia-smi --query-gpu=name,memory.total --format=csv,noheader

echo "== gate: U = I, real-pair kernel (boundary 0, interior sqrt2) =="
$PY experiments/atlas_asc_covariance_gpu.py --init identity --iterations 0 \
    --eval-probes 32 --final-probes 64 --mode descend

echo "== timing: 100 escape steps from a perturbed fold =="
$PY experiments/atlas_asc_covariance_gpu.py --iterations 100 \
    --report-every 20 --eval-every 50 --mode escape
echo SENTINEL_BENCH_DONE
