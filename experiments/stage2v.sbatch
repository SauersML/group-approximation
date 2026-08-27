#!/bin/bash
#SBATCH --partition=v100
#SBATCH --gres=gpu:v100:1
#SBATCH --time=08:00:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64g
#SBATCH --output=/projects/standard/hsiehph/sauer354/nonsofic_existence/experiments/stage2v.out
cd /projects/standard/hsiehph/sauer354/nonsofic_existence/experiments
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
/projects/standard/hsiehph/sauer354/atlas-torch-gpu-venv/bin/python3 atlas_true_criterion_stage2.py atlas-rank5-T_St.json --iterations 100 --report-every 5 --out atlas-stage2v-result.json
