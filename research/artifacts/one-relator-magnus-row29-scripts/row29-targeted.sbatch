#!/bin/bash -l
#SBATCH -J orm-row29
#SBATCH -p agsmall
#SBATCH -t 06:00:00
#SBATCH --mem=2G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/orm-row29/row29-targeted.%j.log
# Lane solve-one-relator-magnus: theory-guided virtual fibring search for row 29,
# G = <a,t | AAttATaTAttaaTT>, over metabelian covers from Delta(s) = -3 + s + s^2.
# Calibration first on row 23 (AAttAATTAtAtaTT, certified at index 3 by the census),
# then row 29, then the independent verifier over both outputs.
cd /scratch.global/sauer354/orm-row29 || exit 1
module load python/3.11 2>/dev/null || true
PY=$(command -v python3.11 || command -v python3)
md5sum vfib.py verify.py vfib_targeted.py "$0"
echo "== calibration row 23"
timeout 1800 $PY vfib_targeted.py AAttAATTAtAtaTT 7 3 30 2 60 1 > cal23.out 2>&1; echo "cal rc=$?"
tail -3 cal23.out
echo "== row 29 targeted"
t0=$(date +%s)
timeout 19000 $PY vfib_targeted.py AAttATaTAttaaTT 61 6 110 2 300 1 > row29.out 2>&1; rc=$?
echo "== row29 rc=$rc seconds=$(( $(date +%s) - t0 )) candidates=$(grep -m1 '^CANDIDATES' row29.out) monic=$(grep -c '^MONIC' row29.out) cert=$(grep -c '^CERT' row29.out) done=$(grep -c '^DONE' row29.out)"
echo "== verify"
$PY verify.py cal23.out row29.out > verify.out 2>&1; echo "verify rc=$?"
cat verify.out | tail -5
echo ALLDONE
