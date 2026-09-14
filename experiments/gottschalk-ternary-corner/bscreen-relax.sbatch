#!/bin/bash
#SBATCH --job-name=gk3b-rel
#SBATCH --time=06:00:00
#SBATCH --mem=24G
#SBATCH --cpus-per-task=1
#SBATCH --array=0-2
#SBATCH --output=/scratch.global/sauer354/gk3-ternary-bilinear/runs/rel-%A_%a.log
# Linearized bilinear relaxations. UNSAT excludes every lambda of the affine lift space at once.
set -euo pipefail
D=/scratch.global/sauer354/gk3-ternary-bilinear
cd $D/code
case $SLURM_ARRAY_TASK_ID in
  0) ARGS="--family mix2 --lift-radius 2 --radius 4" ;;
  1) ARGS="--family mix2 --lift-radius 3 --radius 3" ;;
  2) ARGS="--family mix --lift-radius 1 --radius 1" ;;
esac
$D/venv/bin/python bscreen.py --mode relax $ARGS --max-d 400 --out $D/runs/rel-$SLURM_ARRAY_TASK_ID.json
echo EXIT=$?
