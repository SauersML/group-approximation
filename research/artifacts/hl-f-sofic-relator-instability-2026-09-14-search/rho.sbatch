#!/bin/bash
#SBATCH --job-name=frho-exact
#SBATCH --partition=amdsmall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=32
#SBATCH --mem=4G
#SBATCH --time=02:00:00
#SBATCH --output=/scratch.global/sauer354/hl-f-sofic-relator-instability/frho.%j.log
cd /scratch.global/sauer354/hl-f-sofic-relator-instability || exit 1
export OMP_NUM_THREADS=32
for m in 7 8 9 10 11 12; do date; ./rho $m > rho.$m.out; echo done $m; done
date; echo ALLDONE
