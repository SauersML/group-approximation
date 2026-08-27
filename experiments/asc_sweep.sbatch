#!/bin/bash
#SBATCH --job-name=asc-sweep
#SBATCH --partition=a100-4
#SBATCH --gres=gpu:a100:1
#SBATCH --time=01:20:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/asc-sweep.out
set -uo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
PY=/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3
nvidia-smi --query-gpu=name --format=csv,noheader

# The Pareto curve of (ASCq): for each pinned covariance tau, how small can
# the packet defect be?  Run it twice -- boundary only, where the exact
# characteristic-two countermodel says no collapse is forced, and boundary
# plus the one interior separator, which is the packet the open claim is
# actually about.  The gap between the two curves is what item 5 of
# `research/atlas-two-s3-covariance-collapse` asks for, measured.
for TAU in 0.001 0.01 0.025 0.1 0.5; do
  LAM=$($PY -c "print(max(20.0, 2.0/$TAU))")
  for PACKET in certified,boundary,phase certified,boundary,phase,interior; do
    TAG=$(echo "$PACKET" | grep -q interior && echo full || echo bdry)
    echo "== pin tau=$TAU packet=$TAG lam=$LAM =="
    $PY experiments/atlas_asc_covariance_gpu.py \
        --mode pin --tau "$TAU" --lam "$LAM" --packet "$PACKET" \
        --init perturbed --init-scale 0.1 --iterations 400 \
        --report-every 200 --eval-every 200 --time-limit 300 \
        --out "experiments/asc-pin-${TAG}-${TAU}.jsonl"
  done
done
echo SENTINEL_SWEEP_DONE
