#!/bin/bash
# cert_flat.sh -- phase-locality test over ALL Y-times (rtm_cert, 4e6 steps, L = 8, K = 3, radius 4k + 2, i.e. mod 2
# at radius 6, mod 4 at 10, mod 8 at 14) for the flat-gap machines that the radius-10 return test left undecided
# (no return from the early reference, or all returns = 0 mod 8). Stops after 500 s; prints next=I to resume.
# Lane gq-nv-obstruct, 2026-09-18. MSI only; single core; each call <= 10 min.
# Usage: bash cert_flat.sh FROM        (1-based line of s63_undecided.txt; output appended to s63_cert_flat.out)
set -u
cd /projects/standard/hsiehph/sauer354/gqsrc/gq-nv-obstruct
[ -s s63_undecided.txt ] || grep -E 'n_mod8=\{0,\}|returns_n=\[\]' s63_recur_flat.out > s63_undecided.txt
FROM=$1; i=0; S=$(date +%s); mkdir -p s63_cf
while read -r line; do
  i=$((i + 1)); [ $i -lt $FROM ] && continue
  [ $(( $(date +%s) - S )) -gt 500 ] && { echo "next=$i"; exit 0; }
  B=$(echo "$line" | sed 's/.*beta=\([0-9,]*\).*/\1/'); ST=$(echo "$line" | sed 's/.*start=\([0-9]*\).*/\1/')
  d=s63_cf/$i; mkdir -p $d; cd $d
  C=$(timeout 60 ../../rtm_cert 6 3 21 $B $ST 0 4000000 8 3 4 2 | grep '^k=' | sed 's/k=\([0-9]\) radius=\([0-9]*\) distinct=\([0-9]*\) conflicts=\([0-9]*\)/\1:\2:\3:\4/' | tr '\n' ' ')
  echo "machine $i beta=$B start=$ST cert=[$C]" >> ../../s63_cert_flat.out
  cd ../..
done < s63_undecided.txt
echo "next=END"
