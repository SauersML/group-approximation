#!/bin/bash
#SBATCH --job-name=asc-tangent
#SBATCH --partition=a100-4
#SBATCH --gres=gpu:a100:1
#SBATCH --time=00:45:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/asc-tangent.out
set -uo pipefail
cd /projects/standard/hsiehph/sauer354/nonsofic_existence
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
PY=/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3
echo "== full packet: boundary + interior separator =="
$PY experiments/atlas_asc_tangent_ratio.py --iterations 300 --eval-every 50 \
    --packet certified,boundary,phase,interior \
    --out experiments/asc-tangent-full.jsonl
echo "== boundary only: what the interior word buys =="
$PY experiments/atlas_asc_tangent_ratio.py --iterations 300 --eval-every 50 \
    --packet certified,boundary,phase \
    --out experiments/asc-tangent-bdry.jsonl
echo SENTINEL_TANGENT_DONE
