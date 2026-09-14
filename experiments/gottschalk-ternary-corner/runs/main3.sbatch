#!/bin/bash
#SBATCH -p msismall
#SBATCH -t 04:00:00
#SBATCH -c 1
#SBATCH --mem=24G
#SBATCH -a 0-2
#SBATCH -o /scratch.global/sauer354/gk3-ternary-fullness/main3-%A_%a.log
module load python3
cd /scratch.global/sauer354/gk3-ternary-fullness/code
case $SLURM_ARRAY_TASK_ID in
  0) python3 pscreen.py --family mix2 --lift-radius 1 --radius 3 --level 2 --samples 6 --out ../run3-mix2-r3-l2.json ;;
  1) python3 pscreen.py --family mix2 --lift-radius 2 --radius 4 --level 2 --samples 6 --out ../run3-mix2-r4-l2.json ;;
  2) python3 pscreen.py --family mix --lift-radius 1 --radius 2 --level 2 --samples 4 --out ../run3-mix-r2-l2.json ;;
esac
echo EXIT=$?
