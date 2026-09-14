#!/bin/bash -l
#SBATCH -J vtc
#SBATCH -p agsmall
#SBATCH -t 03:00:00
#SBATCH --mem=512M
#SBATCH -c 1
#SBATCH --array=0-25%12
#SBATCH -o /scratch.global/sauer354/vplanted/vtc.%A_%a.log
# Exact transitive depth-first search (budget 0) with 4 restarts of at most 2e7 nodes each.
# Tasks 0-23: planted S5 control, k in {48,72,96,120}, heur in {0,1,2}, seeds 1-2.
# Tasks 24-25: V at k=48, heur 0, seeds 1-2 (no exact model can exist; exhaustion check).
cd /scratch.global/sauer354/vplanted || exit 1
md5sum vtc.c vtc rel_V.txt rel_CTRL.txt "$0"
i=$SLURM_ARRAY_TASK_ID
if [ "$i" -lt 24 ]; then
  KS=(48 72 96 120); mode=CTRL
  k=${KS[$(( i / 6 ))]}; heur=$(( (i % 6) / 2 )); seed=$(( i % 2 + 1 ))
else
  mode=V; k=48; heur=0; seed=$(( i - 23 ))
fi
t0=$(date +%s)
./vtc $k rel_$mode.txt $seed 4 20000000 0 1 0 $heur
echo "== task $i mode=$mode k=$k heur=$heur seed=$seed seconds=$(( $(date +%s) - t0 ))"
echo ALLDONE
