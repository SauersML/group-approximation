#!/bin/bash
#SBATCH --job-name=gk3-fas-probe
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=1 --mem=8G --time=6:00:00
#SBATCH --output=/scratch.global/sauer354/gk3-four-address-survivors/probe.%j.log
D=/scratch.global/sauer354/gk3-four-address-survivors
cd $D || exit 9
module load python/3.10.10-gcc-8.2.0-sanagub 2>/dev/null || true
PY=$(command -v python3.10 || command -v python3)
GAP=/scratch.global/sauer354/solve-kl-counterexample-search/gap-4.13.1/gap
mkdir -p work-probe
echo "start=$(date -Is) host=$(hostname) py=$PY"
md5sum replay.py search.py flip1.json analyze3.json dflip3.json
RULES="967 971 2183 2195 2215 2229 2449 2481 2759 2771 2773 2789 3025 3041 3815 4081 6279 6299 6309 6311 6371 6565 6893 7913 7929 10665"
$PY search.py flip1.json analyze3.json dflip3.json $GAP work-probe probe $RULES > probe.json.tmp 2> probe.stderr && mv probe.json.tmp probe.json
echo "exit=$? done=$(date -Is)"; tail -3 probe.stderr
touch DONE-probe
