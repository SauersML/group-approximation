#!/bin/bash
#SBATCH --job-name=asc-probe
#SBATCH --partition=a100-4
#SBATCH --gres=gpu:a100:1
#SBATCH --time=00:35:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/asc-probe.out
set -uo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
PY=/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3
RUN="$PY experiments/atlas_asc_covariance_gpu.py --iterations 400 \
     --report-every 100 --eval-every 100 --time-limit 420"
nvidia-smi --query-gpu=name --format=csv,noheader

echo "== A: descend from Haar -- can the packet defect fall with cov left free =="
$RUN --mode descend --init random --out experiments/asc-A.jsonl

echo "== B: descend from a lightly perturbed classical fold =="
$RUN --mode descend --init perturbed --init-scale 0.1 \
     --out experiments/asc-B.jsonl

echo "== C: pin cov at 1/40 from Haar =="
$RUN --mode pin --tau 0.025 --lam 8 --init random --out experiments/asc-C.jsonl

echo "== D: interior word alone from the fold -- what does killing it cost =="
$RUN --mode descend --init perturbed --init-scale 0.1 --packet interior \
     --out experiments/asc-D.jsonl
echo SENTINEL_PROBE_DONE
