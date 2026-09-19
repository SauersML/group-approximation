#!/bin/bash
# recur_all.sh -- for every bounded-overhead 6+6/3 candidate (s63_bounded_all.txt, from rank_all.sh summary):
# (1) Y = zero-overhead local types (rtm_cert, 4e5 steps, last 8 levels); (2) return-time test at radius 10
# (rtm_recur, 4e6 steps); (3) if no return has n odd mod 8 away from 0, the per-level maximal Y-gap
# (rtm_gaps, 1.6e7 steps), last 6 levels. Stops starting new machines after 500 s and prints next=I to resume.
# Lane gq-nv-obstruct, 2026-09-18. MSI only; single core; each call <= 10 min.
# Usage: bash recur_all.sh FROM        (1-based line of s63_bounded_all.txt)
set -u
cd /projects/standard/hsiehph/sauer354/gqsrc/gq-nv-obstruct
FROM=$1; i=0; S=$(date +%s); mkdir -p s63_ra
while read -r line; do
  i=$((i + 1)); [ $i -lt $FROM ] && continue
  [ $(( $(date +%s) - S )) -gt 500 ] && { echo "next=$i"; exit 0; }
  B=$(echo "$line" | sed 's/.*beta=\([0-9,]*\).*/\1/'); ST=$(echo "$line" | sed 's/.*start=\([0-9]*\).*/\1/')
  d=s63_ra/$i; mkdir -p $d; cd $d
  timeout 40 ../../rtm_cert 6 3 21 $B $ST 0 400000 8 1 0 3 > cert.out 2>&1
  NY=$(wc -l < yt.txt 2>/dev/null || echo 0); NY=$((NY + 0))
  REC=""; M8=""; GAPS=""
  if [ $NY -gt 0 ]; then
    REC=$(timeout 40 ../../rtm_recur 6 3 21 $B $ST 0 4000000 10 10 2 6 | grep '^return' | awk '{print $3}' | sed 's/n=//' | tr '\n' ' ')
    M8=$(for x in $REC; do echo $((x % 8)); done | sort -u | tr '\n' ',')
    case "$M8" in ""|"0,") GAPS=$(timeout 60 ../../rtm_gaps 6 3 21 $B $ST 0 16000000 0 | grep '^lev' | tail -6 | sed 's/.*lev=\([0-9]*\).*maxgap=\([0-9]*\).*/\1:\2/' | tr '\n' ' ');; esac
  fi
  echo "machine $i beta=$B start=$ST Ytypes=$NY returns_n=[$REC] n_mod8={$M8} gaps=[$GAPS]"
  cd ../..
done < s63_bounded_all.txt
echo "next=END"
