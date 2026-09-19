#!/bin/bash
# ygap_all.sh -- the bounded-junction filter (rtm_ygap_batch, 3e5 steps, L = 6) over EVERY 6+6/3 candidate,
# one chunk of 50,000 lines of s63_all.txt per call. The overhead-growth ranking of rank_all.sh is not this
# filter: it also counts non-Y types. Lane gq-nv-obstruct, 2026-09-18. MSI only; single core; each call <= 10 min.
# Usage: bash ygap_all.sh CHUNK | summary
set -u
cd /projects/standard/hsiehph/sauer354/gqsrc/gq-nv-obstruct
N=$(wc -l < s63_all.txt); mkdir -p s63_yg
if [ "$1" = summary ]; then
  echo "candidates: $N  chunks done: $(grep -l YGAP_DONE s63_yg/*.out | wc -l)"
  cat s63_yg/*.out | grep '^YGAP_DONE' | awk '{split($2,a,"="); split($3,b,"="); s+=a[2]; w+=b[2]} END {print "seen=" s, "withY=" w}'
  cat s63_yg/*.out | grep '^YGAP ' | awk '{split($3,a,"="); split($4,b,"="); if (a[2] <= b[2]) print}' > s63_ygap_flat.txt
  echo "non-growing Y-gap (late <= early): $(wc -l < s63_ygap_flat.txt)"
else
  c=$1; lo=$((c * 50000 + 1)); hi=$(((c + 1) * 50000))
  [ $lo -gt $N ] && { echo NOCHUNK; exit 0; }
  sed -n "${lo},${hi}p" s63_all.txt | timeout 580 ./rtm_ygap_batch 6 3 300000 6 > s63_yg/$c.out
  echo "chunk $c $(tail -1 s63_yg/$c.out)"
fi
