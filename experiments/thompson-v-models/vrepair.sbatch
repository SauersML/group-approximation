#!/bin/bash -l
#SBATCH -J vrepair
#SBATCH -p agsmall
#SBATCH -t 03:00:00
#SBATCH --mem=512M
#SBATCH -c 1
#SBATCH --array=0-35%10
#SBATCH -o /scratch.global/sauer354/vplanted/vrep.%A_%a.log
# Repair-move annealing. Tasks 0-17: planted S5 control; tasks 18-35: V.
# Per mode: k in {48,120,240}; schedule P1 (T 2 -> 0.05, noise 0.1) or P2 (T = 0.5, noise 0.05);
# seeds 1-3. Iterations: 3e7 at k=48, 6e7 at k=120 and 240.
cd /scratch.global/sauer354/vplanted || exit 1
md5sum vrepair.c vrepair rel_V.txt rel_CTRL.txt "$0"
i=$SLURM_ARRAY_TASK_ID
MODES=(CTRL V); KS=(48 120 240); ITS=(30000000 60000000 60000000)
mode=${MODES[$(( i / 18 ))]}; r=$(( i % 18 ))
ki=$(( r / 6 )); k=${KS[$ki]}; it=${ITS[$ki]}; p=$(( (r % 6) / 3 )); seed=$(( r % 3 + 1 ))
if [ "$p" -eq 0 ]; then T0=2.0; T1=0.05; nz=0.1; else T0=0.5; T1=0.5; nz=0.05; fi
t0=$(date +%s)
./vrepair $k $it $T0 $T1 $nz $seed rel_$mode.txt
echo "== task $i mode=$mode k=$k sched=P$(( p + 1 )) seed=$seed seconds=$(( $(date +%s) - t0 ))"
echo ALLDONE
