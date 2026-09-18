#!/bin/sh
# Reproduce all outputs of this directory (single-threaded; about an hour in total).
set -e
gcc -O2 -o pairx pairx.c
python3 certify_r.py 1 1 -1,0,1 13 14 > cert_plain_R101_K1.txt
NZREF=1 RIGID=1 python3 certify_r.py 1 1 -1,0,1 11 14 > cert_nzref_rigid_R101_K1.txt
NZREF=1 python3 blockcheck_r.py -1,0,1 > blockcheck_nzref_R101.txt
NZREF=1 RIGID=1 python3 blockcheck_r.py -1,0,1 > blockcheck_nzref_rigid_R101.txt
for R in 0,1 -1,0,1 -2,-1,0,1,2 -3,-2,-1,0,1,2,3; do
  ./pairx 1 $R 3 0 1 3 3 0 1 4 > srig_tmp.txt
  python3 crit.py srig_tmp.txt 3 | sed "s/^srig_tmp.txt/S_rig c=1 R=$R/"
done > srig_obstruction.txt
rm -f srig_tmp.txt
