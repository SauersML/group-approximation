#!/bin/bash
#SBATCH --job-name=gk3-fas-replay
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=1 --mem=8G --time=4:00:00
#SBATCH --output=/scratch.global/sauer354/gk3-four-address-survivors/replay.%j.log
D=/scratch.global/sauer354/gk3-four-address-survivors
cd $D || exit 9
module load python/3.10.10-gcc-8.2.0-sanagub 2>/dev/null || true
PY=$(command -v python3.10 || command -v python3)
GAP=/scratch.global/sauer354/solve-kl-counterexample-search/gap-4.13.1/gap
MODE=${MODE:-replay}
mkdir -p work-$MODE
echo "start=$(date -Is) host=$(hostname) mode=$MODE py=$PY"
md5sum replay.py flip1.json analyze3.json dflip3.json
$PY selftest.py $GAP work-selftest > selftest.out 2>&1; echo "selftest exit=$?"; tail -30 selftest.out
$PY replay.py flip1.json analyze3.json dflip3.json $GAP work-$MODE $MODE > $MODE.json.tmp 2> $MODE.stderr && mv $MODE.json.tmp $MODE.json
echo "exit=$? done=$(date -Is)"; tail -3 $MODE.stderr
touch DONE-$MODE
