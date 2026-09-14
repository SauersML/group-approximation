#!/bin/bash -l
#SBATCH -J vctrl2
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=512M
#SBATCH -c 1
#SBATCH --array=0-25%10
#SBATCH -o /scratch.global/sauer354/vplanted/vc2.%A_%a.log
# PSL(2,17) control (rel_CTRL2.txt), whose exact gluings through G have components of size 144 or 2448.
# Tasks 0-23: vrepair, mode CTRL2 or V, k in {144,288}, schedule P1 or P2, seeds 1-3, 6e7 iterations.
# Tasks 24-25: vtc exact transitive search on CTRL2 at k=144, heur 0, seeds 1-2, 4 x 2e7 nodes.
cd /scratch.global/sauer354/vplanted || exit 1
md5sum vrepair.c vrepair vtc.c vtc rel_V.txt rel_CTRL2.txt "$0"
i=$SLURM_ARRAY_TASK_ID
t0=$(date +%s)
if [ "$i" -lt 24 ]; then
  MODES=(CTRL2 V); KS=(144 288)
  mode=${MODES[$(( i / 12 ))]}; r=$(( i % 12 )); k=${KS[$(( r / 6 ))]}; p=$(( (r % 6) / 3 )); seed=$(( r % 3 + 1 ))
  if [ "$p" -eq 0 ]; then T0=2.0; T1=0.05; nz=0.1; else T0=0.5; T1=0.5; nz=0.05; fi
  ./vrepair $k 60000000 $T0 $T1 $nz $seed rel_$mode.txt
  echo "== task $i vrepair mode=$mode k=$k sched=P$(( p + 1 )) seed=$seed seconds=$(( $(date +%s) - t0 ))"
else
  seed=$(( i - 23 ))
  ./vtc 144 rel_CTRL2.txt $seed 4 20000000 0 1 0 0
  echo "== task $i vtc mode=CTRL2 k=144 seed=$seed seconds=$(( $(date +%s) - t0 ))"
fi
echo ALLDONE
