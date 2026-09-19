#!/bin/bash
# recur_flat.sh -- return-time test (radius 10) for the machines whose Y-gap is flat at 3.2e7 steps
# (s63_flat32m.txt, from rtm_ygap_batch 6 3 32000000 6 6). Y = zero-overhead types of rtm_cert (4e6 steps, L = 8);
# returns from rtm_recur (1.6e7 steps). Stops starting new machines after 500 s and prints next=I to resume.
# Lane gq-nv-obstruct, 2026-09-18. MSI only; single core; each call <= 10 min.
# Usage: bash recur_flat.sh FROM        (1-based line of s63_flat32m.txt; output appended to s63_recur_flat.out)
set -u
cd /projects/standard/hsiehph/sauer354/gqsrc/gq-nv-obstruct
FROM=$1; i=0; S=$(date +%s); mkdir -p s63_rf
while read -r line; do
  i=$((i + 1)); [ $i -lt $FROM ] && continue
  [ $(( $(date +%s) - S )) -gt 500 ] && { echo "next=$i"; exit 0; }
  B=$(echo "$line" | sed 's/.*beta=\([0-9,]*\).*/\1/'); ST=$(echo "$line" | sed 's/.*start=\([0-9]*\).*/\1/')
  G=$(echo "$line" | sed 's/.*late=\([0-9]*\).*/\1/')
  d=s63_rf/$i; mkdir -p $d; cd $d
  timeout 40 ../../rtm_cert 6 3 21 $B $ST 0 4000000 8 1 1 3 > cert.out 2>&1
  NY=$(wc -l < yt.txt 2>/dev/null || echo 0); NY=$((NY + 0)); REC=""; M8=""
  if [ $NY -gt 0 ]; then
    REC=$(timeout 40 ../../rtm_recur 6 3 21 $B $ST 0 16000000 10 10 2 6 | grep '^return' | awk '{print $3}' | sed 's/n=//' | tr '\n' ' ')
    M8=$(for x in $REC; do echo $((x % 8)); done | sort -u | tr '\n' ',')
  fi
  echo "machine $i beta=$B start=$ST gap=$G Ytypes=$NY returns_n=[$REC] n_mod8={$M8}" >> ../../s63_recur_flat.out
  cd ../..
done < s63_flat32m.txt
echo "next=END"
