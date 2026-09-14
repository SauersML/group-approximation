#!/bin/bash
#SBATCH --job-name=ac-fs-t6
#SBATCH --partition=agsmall
#SBATCH --account=hsiehph
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=48
#SBATCH --mem=24G
#SBATCH --time=10:00:00
#SBATCH --output=/scratch.global/sauer354/hl-andrews-curtis/fs/t6-%j.log
set -euo pipefail
D=/scratch.global/sauer354/hl-andrews-curtis/fs
cd $D
g++ -O3 -march=native -std=c++17 -fopenmp -o fsenum6 fsenum.cpp
export OMP_NUM_THREADS=48
# regression: the stack-matrix build must reproduce the calibrated t<=5 totals
for t in 3 4 5; do ./fsenum6 $t reg-t$t.txt 2> reg-t$t.err; cmp reg-t$t.txt classes-t$t.txt && echo "REGRESSION_OK t=$t"; done
/usr/bin/time -v ./fsenum6 6 classes-t6.txt 2> run-t6.err
grep -E "TOTAL|FAIL|Elapsed|Maximum resident" run-t6.err
echo T6_DONE
