#!/bin/bash
#SBATCH --job-name=asc-exact-sub
#SBATCH --partition=a100-4
#SBATCH --gres=gpu:a100:1
#SBATCH --time=00:35:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=120g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/asc-exact-sub.out
set -uo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
PY=/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3
for SEL in tangent5 certified24; do
  echo "== words=$SEL =="
  $PY experiments/atlas_asc_tangent_exact.py --words $SEL \
      --out experiments/asc-exact-$SEL.json
done
echo SENTINEL_SUBSETS_DONE
