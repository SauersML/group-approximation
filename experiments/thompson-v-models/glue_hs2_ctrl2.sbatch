#!/bin/bash -l
#SBATCH -J vhs3
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=3G
#SBATCH -c 1
#SBATCH --array=0-17%12
#SBATCH -o /scratch.global/sauer354/hl-v-approximation/r3/vhs3.%A_%a.log
# Calibrated unitary gluing runs against the PSL(2,17) control, which has no 24-point components.
# Tasks 0-11: CTRL2, N in {144, 288} x method in {descent, restart, anneal} x seed in {1, 2}.
# Tasks 12-17: V at N = 144, method in {descent, restart, anneal} x seed in {1, 2}.
cd /scratch.global/sauer354/hl-v-approximation/r3 || exit 1
module load python/3.10.10-gcc-8.2.0-sanagub
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
md5sum glue_hs2.py glue_hs.py texwords.py rel_V.txt rel_CTRL2.txt gen_ctrl2.log "$0"
i=$SLURM_ARRAY_TASK_ID
METHODS=(descent restart anneal)
if [ "$i" -lt 12 ]; then
  mode=CTRL2; NS=(144 288); N=${NS[$(( i / 6 ))]}; r=$(( i % 6 ))
else
  mode=V; N=144; r=$(( i - 12 ))
fi
method=${METHODS[$(( r / 2 ))]}; seed=$(( r % 2 + 1 ))
if [ "$N" -eq 144 ]; then it=4000; else it=2000; fi
t0=$(date +%s)
python3 glue_hs2.py --task "$mode $N $seed $method" --iters $it --out r3_$i.json
echo "== task $i mode=$mode N=$N method=$method seed=$seed iters=$it seconds=$(( $(date +%s) - t0 ))"
echo ALLDONE
