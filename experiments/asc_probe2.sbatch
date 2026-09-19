#!/bin/bash
#SBATCH --job-name=asc-probe2
#SBATCH --partition=a100-4
#SBATCH --gres=gpu:a100:1
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/asc-probe2.out
set -uo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
PY=/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3
RUN="$PY experiments/atlas_asc_covariance_gpu.py --iterations 300 \
     --report-every 100 --eval-every 100 --time-limit 300"
echo "== A: descend from Haar, geodesic steps =="
$RUN --mode descend --init random --out experiments/asc-A.jsonl
echo "== B: descend from the fold, boundary only, cov free =="
$RUN --mode descend --init perturbed --init-scale 0.1 \
     --packet certified,boundary,phase --out experiments/asc-B.jsonl
echo SENTINEL_PROBE2_DONE
