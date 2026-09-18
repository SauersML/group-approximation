#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 1
#SBATCH --mem=6G
#SBATCH -t 00:10:00
#SBATCH -J bhf35-cert
#SBATCH -o /projects/standard/hsiehph/sauer354/bh-free-35/cert/job-%j.out
set -u
module load sagemath/10.7
export DOT_SAGE=/projects/standard/hsiehph/sauer354/bh-free-35/cert/dotsage
export TMPDIR=/projects/standard/hsiehph/sauer354/bh-free-35/cert/tmp
export OMP_NUM_THREADS=1
mkdir -p $DOT_SAGE $TMPDIR
cd /projects/standard/hsiehph/sauer354/bh-free-35/cert
timeout 575 python3 /projects/standard/hsiehph/sauer354/bh-free-35/cert/driver.py /projects/standard/hsiehph/sauer354/bh-free-35/cert/run-$SLURM_JOB_ID
echo "driver rc=$?"
