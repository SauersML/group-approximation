#!/bin/bash
#SBATCH --job-name=gk3b-exh
#SBATCH --time=04:00:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --array=0-31%8
#SBATCH --output=/scratch.global/sauer354/gk3-ternary-bilinear/runs/exh-%A_%a.log
# 32 tasks: tasks 0-15 use C = mix2 ball of radius 3, tasks 16-31 radius 4.
# Each radius enumerates lambda in F_3^d (d = 9 expected) in 16 equal shards.
set -euo pipefail
D=/scratch.global/sauer354/gk3-ternary-bilinear
cd $D/code
T=$SLURM_ARRAY_TASK_ID
if [ "$T" -lt 16 ]; then R=3; S=$T; else R=4; S=$((T - 16)); fi
N=19683
W=$(( (N + 15) / 16 ))
LO=$(( S * W )); HI=$(( LO + W ))
$D/venv/bin/python bscreen.py --mode exhaust --family mix2 --lift-radius 2 --radius $R \
  --lo $LO --hi $HI --out $D/runs/exh-r$R-s$S.json
echo EXIT=$?
