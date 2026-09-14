#!/bin/bash
#SBATCH --job-name=gk3b-mul
#SBATCH --time=06:00:00
#SBATCH --mem=24G
#SBATCH --cpus-per-task=1
#SBATCH --array=0-18%8
#SBATCH --output=/scratch.global/sauer354/gk3-ternary-bilinear/runs/mul-%A_%a.log
# beta support multiplied by a finite subgroup K (absorbs units of eps_- F_3[K] over 1).
# tasks 0-15: exhaust, mult klein, C = mix2 ball radius 3, 16 shards of F_3^9.
# tasks 16-18: relaxations (klein r4, e2 r4, gl2 r3).
set -euo pipefail
D=/scratch.global/sauer354/gk3-ternary-bilinear
cd $D/code2
T=$SLURM_ARRAY_TASK_ID
if [ "$T" -lt 16 ]; then
  N=19683; W=$(( (N + 15) / 16 )); LO=$(( T * W )); HI=$(( LO + W ))
  $D/venv/bin/python bscreen.py --mode exhaust --family mix2 --lift-radius 2 --radius 3 --mult klein \
    --lo $LO --hi $HI --out $D/runs/mul-exh-klein-r3-s$T.json
else
  case $T in
    16) ARGS="--radius 4 --mult klein" ;;
    17) ARGS="--radius 4 --mult e2" ;;
    18) ARGS="--radius 3 --mult gl2" ;;
  esac
  $D/venv/bin/python bscreen.py --mode relax --family mix2 --lift-radius 2 $ARGS --max-d 400 \
    --out $D/runs/mul-rel-$T.json
fi
echo EXIT=$?
