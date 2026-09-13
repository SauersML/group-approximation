#!/bin/bash -l
#SBATCH -J vcollapse
#SBATCH -p agsmall
#SBATCH -t 01:30:00
#SBATCH --mem=512M
#SBATCH -c 1
#SBATCH --array=0-35%8
#SBATCH -o /scratch.global/sauer354/vcollapse/va.%A_%a.log
# Annealing search for fixed-point-free almost-homomorphisms V -> Sym(k) (Bleak-Quick (2.4)).
cd /scratch.global/sauer354/vcollapse || exit 1
[ -x vanneal ] || gcc -O2 -o vanneal vanneal.c -lm
md5sum vanneal.c "$0"
KS=(12 24 48 96 192 384); i=$SLURM_ARRAY_TASK_ID
k=${KS[$(( i / 6 ))]}; seed=$(( i % 6 + 1 ))
it=$(( 4000000 ))
t0=$(date +%s)
./vanneal $k $it 0.05 0.0005 $seed
echo "== task $i k=$k seed=$seed seconds=$(( $(date +%s) - t0 ))"
echo ALLDONE
