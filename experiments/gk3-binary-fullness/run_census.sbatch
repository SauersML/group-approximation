#!/bin/bash
#SBATCH -p msismall
#SBATCH -t 04:00:00
#SBATCH -c 6
#SBATCH --mem=24G
#SBATCH -J gk3-cover
#SBATCH -o /scratch.global/sauer354/gk3-binary-fullness/logs/%x-%j.log
# Linear census of rank-deficient tower coverings over V. Outputs only under the lane scratch dir.
set -euo pipefail
W=/scratch.global/sauer354/gk3-binary-fullness
cd "$W"
PY=/usr/bin/python3.11
$PY tower_cover_census.py --mode controls --budget 3000 --samples 8 --seed 11 --dense 6000 --out out/controls.jsonl &
$PY tower_cover_census.py --mode census --rs 2,3 --budget 20000 --samples 6 --seed 21 --leaves 5 --dense 0 --out out/census-r23.jsonl &
$PY tower_cover_census.py --mode census --rs 4,5 --budget 20000 --samples 6 --seed 31 --leaves 5 --dense 0 --out out/census-r45.jsonl &
$PY tower_cover_census.py --mode census --rs 6,7 --budget 20000 --samples 6 --seed 41 --leaves 5 --dense 0 --out out/census-r67.jsonl &
$PY tower_cover_census.py --mode census --rs 8 --budget 20000 --samples 8 --seed 51 --leaves 6 --dense 0 --out out/census-r8.jsonl &
$PY tower_cover_census.py --mode census --rs 2,4,8 --budget 3000 --samples 10 --seed 61 --leaves 4 --dense 6000 --out out/census-crosscheck.jsonl &
wait
echo ALL_DONE
