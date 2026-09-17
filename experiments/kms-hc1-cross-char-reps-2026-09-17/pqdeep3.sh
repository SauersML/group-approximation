#!/bin/sh
# One GAP process per configuration (pqdeep2.g hit its 1200s limit inside B2 p=7 class 30).
# B2 (Gamma_p itself) towers grow geometrically (5^286 at class 12, 7^685 at class 14; see
# experiments/kms-coprime-extensions-2026-09-17/pq*.out), so only the A2 quotient is pushed further.
# The first two runs (5/50, 11/40) exceeded the 1200s limit; a planned 13/36 run was stopped and
# replaced by the moderate-depth runs 11/24 and 13/20, which record the tower for two more primes.
one() { echo "Read(\"pqlib.g\"); run(\"$1\",$2,$3); QUIT;" > cfg_$1_$2_$3.g; nice -n 10 timeout 1200 gap -q -o 2g cfg_$1_$2_$3.g 2>&1 || echo "  $1 p=$2 class<=$3: killed or failed (exit $?)"; rm -f cfg_$1_$2_$3.g; }
[ "$1" = rest ] || { one A2 5 50; one A2 11 40; }
one A2 11 24
one A2 13 20
