#!/bin/bash
#SBATCH --job-name=gk3-enum4
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=4 --mem=16G --time=6:00:00
#SBATCH --output=/scratch.global/sauer354/gk3-strict-census-4/run_enum.%j.log
# Forward tables of shapes 3x4, 4x3 (survivors of the rule-independent filters) and a count of 4x4.
cd /scratch.global/sauer354/gk3-strict-census-4 || exit 9
echo "start=$(date -Is) host=$(hostname)"
md5sum enum4.py
P=/usr/bin/python3.12
$P enum4.py 3 4 surv_3x4.jsonl > enum_3x4.out 2>&1 &
$P enum4.py 4 3 surv_4x3.jsonl > enum_4x3.out 2>&1 &
timeout 18000 $P enum4.py 4 4 /dev/null count > enum_4x4_count.out 2>&1 &
wait
cat enum_3x4.out enum_4x3.out enum_4x4_count.out
echo "end=$(date -Is) DONE"
