#!/bin/bash
# Replays the scale-8 certificates for k = 2..8 (route research/z8-rips-contractible-at-scale-8-proof.md).
# Run from this directory.  Needs g++ with BMI2 (-march=native on x86-64), python3, and the sibling directory
# ../zn-rips-lifted-domination-core-2026-09-18 for vcert2.cpp.  Every step is single-threaded.
set -e
g++ -O2 -march=native -o kzv kzv.cpp
g++ -O2 -march=native -o kzv3 kzv3.cpp
g++ -O2 -o vcert2 ../zn-rips-lifted-domination-core-2026-09-18/vcert2.cpp
mkdir -p work
# k = 2..7: one certificate each, replayed from all of Lmax_k
for k in 2 3 4 5 6 7; do
  python3 genL.py $k 8 work/L$k.txt
  gunzip -c certs/cert-8-8-k$k.txt.gz > work/c$k.txt
  ./kzv $k 8 work/L$k.txt work/c$k.txt
done
# k = 8, prefix: plain (D) moves from Lmax_8 (tags A and D), exhaustive replay; writes the end set a8_8
gunzip -c certs/cert-8-8-k8-prefix.txt.gz > work/p8.txt
set +e; ./vcert2 8 8 -o work/a8_8.txt work/p8.txt; c=$?; set -e
[ $c = 2 ] || { echo "prefix: unexpected vcert2 exit $c"; exit 1; }   # 2 = every move valid, end set larger than {e_8}
# k = 8, link part: compact D/K lines from a8_8 to {e_8}, replayed in budgeted pieces (each piece ends at a line
# boundary; the next piece starts from the set the previous one wrote and continues with the remaining lines)
gunzip -c certs/cert-8-8-k8-link.txt.gz > work/rem.txt
cp work/a8_8.txt work/cur.txt
while true; do
  set +e; ./kzv3 8 8 work/cur.txt work/rem.txt work/nxt.txt ${BUDGET:-800} | tee work/log; c=${PIPESTATUS[0]}; set -e
  L=$(tail -n 1 work/log)
  if [ $c = 3 ]; then n=$(echo "$L" | sed 's/.* lines=\([0-9]*\) .*/\1/'); tail -n +$((n+1)) work/rem.txt > work/r2; mv work/r2 work/rem.txt; mv work/nxt.txt work/cur.txt
  elif [ $c = 0 ]; then echo "$L" | grep -q 'END={e_k}' && echo "k=8 link part ACCEPT, end set {e_8}"; break
  else echo "k=8 link part FAIL"; exit 1; fi
done
