#!/bin/bash -l
#SBATCH -J vglue
#SBATCH -p agsmall
#SBATCH -t 02:00:00
#SBATCH --mem=512M
#SBATCH -c 1
#SBATCH --array=0-29%10
#SBATCH -o /scratch.global/sauer354/vcollapse/vg.%A_%a.log
cd /scratch.global/sauer354/vcollapse || exit 1
md5sum vglue.c vglue rel_V.txt rel_CTRL.txt "$0"
KS=(48 120 240 480 960); MODES=(V CTRL); i=$SLURM_ARRAY_TASK_ID
mode=${MODES[$(( i / 15 ))]}; r=$(( i % 15 )); k=${KS[$(( r / 3 ))]}; seed=$(( r % 3 + 1 ))
t0=$(date +%s)
./vglue $k 3000000 0.05 0.0005 $seed rel_$mode.txt
echo "== task $i mode=$mode k=$k seed=$seed seconds=$(( $(date +%s) - t0 ))"
echo ALLDONE
