#!/bin/bash
#SBATCH -p msismall
#SBATCH -t 08:00:00
#SBATCH -c 1
#SBATCH --mem=24G
#SBATCH -a 0-2
#SBATCH -o /scratch.global/sauer354/gk3-ternary-fullness/main2-%A_%a.log
module load python3
cd /scratch.global/sauer354/gk3-ternary-fullness/code
case $SLURM_ARRAY_TASK_ID in
  0) python3 pscreen.py --family mix --lift-radius 1 --radius 2 --level 2 --samples 6 --out ../run2-mix-r2-l2.json ;;
  1) python3 pscreen.py --family eld3 --lift-radius 1 --radius 2 --level 2 --samples 4 --out ../run2-eld3-r2-l2.json ;;
  2) python3 pscreen.py --family vwd --lift-radius 2 --radius 3 --level 2 --samples 4 --out ../run2-vwd-r3-l2.json ;;
esac
echo EXIT=$?
