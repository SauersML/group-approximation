#!/bin/bash -l
#SBATCH -J orm-cal2
#SBATCH -p agsmall
#SBATCH -t 03:00:00
#SBATCH --mem=2G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/orm-row29/cal2.%j.log
# Calibrate vfib_targeted2.py on row 23's census certificate cover (k = 10): same enumeration
# rule as vfib.py (POTCAP 60000), then the heuristic forced; plus membership in the affine set.
cd /scratch.global/sauer354/orm-row29 || exit 1
module load python/3.11 2>/dev/null || true
PY=$(command -v python3.11 || command -v python3)
md5sum vfib.py vfib_targeted.py vfib_targeted2.py verify.py certs10.txt "$0"
t0=$(date +%s)
timeout 10000 $PY vfib_targeted2.py calcert AAttAATTAtAtaTT certs10.txt 7 3 30 2 1 60000 40 > cal2.out 2>&1; echo "cal2 rc=$? seconds=$(( $(date +%s) - t0 ))"
cat cal2.out
$PY verify.py cal2.out > cal2.verify 2>&1; echo "verify rc=$?"; tail -3 cal2.verify
echo ALLDONE
