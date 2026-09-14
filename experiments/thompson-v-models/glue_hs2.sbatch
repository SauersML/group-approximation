#!/bin/bash -l
#SBATCH -J vhs2
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=2G
#SBATCH -c 1
#SBATCH --array=0-23%12
#SBATCH -o /scratch.global/sauer354/hl-v-approximation/vhs2.%A_%a.log
# Calibrated unitary gluing runs (glue_hs2.py).
# Tasks: mode in {CTRL, V} x N in {120, 240} x method in {descent, restart, anneal} x seed in {1, 2}.
# CTRL has exact gluings at N divisible by 120 (left regular representation of S5); V has none at any N.
cd /scratch.global/sauer354/hl-v-approximation || exit 1
module load python/3.10.10-gcc-8.2.0-sanagub
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
md5sum glue_hs2.py glue_hs.py texwords.py rel_V.txt rel_CTRL.txt "$0"
i=$SLURM_ARRAY_TASK_ID
MODES=(CTRL V); NS=(120 240); METHODS=(descent restart anneal)
mode=${MODES[$(( i / 12 ))]}; r=$(( i % 12 ))
N=${NS[$(( r / 6 ))]}; r2=$(( r % 6 )); method=${METHODS[$(( r2 / 2 ))]}; seed=$(( r2 % 2 + 1 ))
if [ "$N" -eq 120 ]; then it=4000; else it=2000; fi
t0=$(date +%s)
python3 glue_hs2.py --task "$mode $N $seed $method" --iters $it --out r2_$i.json
echo "== task $i mode=$mode N=$N method=$method seed=$seed iters=$it seconds=$(( $(date +%s) - t0 ))"
echo ALLDONE
