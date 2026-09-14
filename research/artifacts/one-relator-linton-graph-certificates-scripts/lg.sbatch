#!/bin/bash -l
#SBATCH -J mgb-lintongraph
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=4G
#SBATCH -c 4
#SBATCH -o /scratch.global/sauer354/magnus-builder/lg.%j.log
# Lane solve-magnus-graph-builder: Linton graph-of-cyclic-stabilisers certificates.
cd /scratch.global/sauer354/magnus-builder || exit 1
PY=/usr/bin/python3.12
md5sum lintongraph.py census.py census2.py malnormal.py residue-output.txt census3_16.out "$0"
echo "== calib"; timeout 600 $PY lintongraph.py calib > lg_calib.out 2>&1; echo "calib rc=$?"; cat lg_calib.out
( timeout 3000 $PY lintongraph.py words residue-output.txt > lg_l15.out 2>&1; echo "l15 rc=$?" ) &
( timeout 12000 $PY lintongraph.py census 16 > lg_seq16.out 2>&1; echo "seq16 rc=$?" ) &
( timeout 12000 $PY lintongraph.py words census3_16.out > lg_words16.out 2>&1; echo "words16 rc=$?" ) &
wait
for f in lg_l15.out lg_seq16.out lg_words16.out; do echo "== $f"; grep -c '^VERDICT' $f; grep -o -- '-> [A-Z_]*([^)]*)\|-> PASS[A-Z_]*\| NONFREE\| GCD' $f | sort | uniq -c; tail -1 $f; done
echo ALLDONE
