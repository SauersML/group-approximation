#!/bin/bash
#SBATCH --job-name=ac-fs-calib
#SBATCH --partition=agsmall
#SBATCH --account=hsiehph
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=8G
#SBATCH --time=01:00:00
#SBATCH --output=/scratch.global/sauer354/hl-andrews-curtis/fs/calib-%j.log
set -euo pipefail
D=/scratch.global/sauer354/hl-andrews-curtis/fs
cd $D
g++ -O3 -march=native -std=c++17 -fopenmp -o fsenum fsenum.cpp
export OMP_NUM_THREADS=16
for t in 1 2 3 4 5; do
  /usr/bin/time -v ./fsenum $t classes-t$t.txt 2> run-t$t.err || { echo "RUN FAILED t=$t"; cat run-t$t.err; exit 1; }
  grep -E "TOTAL|FAIL" run-t$t.err
  grep -E "Elapsed|Maximum resident" run-t$t.err
done
echo CALIB_DONE
