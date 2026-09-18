#!/bin/bash
# rank_all.sh -- rank EVERY 6+6/3 binary-timing candidate (no frontier-signature dedupe; the dedupe of analyze63.sh
# is lossy: M° has growth 0 but its signature representative has growth 4). One chunk of 50,000 lines per call.
# Lane gq-nv-obstruct, 2026-09-18. MSI only; single core; each call <= 10 min.
# Usage: bash rank_all.sh CHUNK        (CHUNK = 0, 1, ...; prints NOCHUNK past the end)
#        bash rank_all.sh summary      (growth histogram over all ranked chunks; writes s63_bounded_all.txt)
set -u
cd /projects/standard/hsiehph/sauer354/gqsrc/gq-nv-obstruct
[ -s s63_all.txt ] || cat s63/*.out | grep '^PASS' > s63_all.txt
N=$(wc -l < s63_all.txt); mkdir -p s63_rk
if [ "$1" = summary ]; then
  echo "candidates: $N  chunks done: $(grep -l RTM_LEVELS_BATCH_DONE s63_rk/*.out | wc -l)  ranked: $(cat s63_rk/*.out | grep -c RANK)"
  cat s63_rk/*.out | grep RANK | awk '{split($2,a,"="); split($3,b,"="); print "growth=" a[2]-b[2]}' | sort | uniq -c | sort -t= -k2 -n | head -8
  cat s63_rk/*.out | grep RANK | awk '{split($2,a,"="); split($3,b,"="); if (a[2]-b[2] <= 0) print}' > s63_bounded_all.txt
  echo "bounded (growth <= 0): $(wc -l < s63_bounded_all.txt)"
else
  c=$1; lo=$((c * 50000 + 1)); hi=$(((c + 1) * 50000))
  [ $lo -gt $N ] && { echo NOCHUNK; exit 0; }
  sed -n "${lo},${hi}p" s63_all.txt | timeout 580 ./rtm_levels_one 6 3 300000 > s63_rk/$c.out
  echo "chunk $c lines $lo-$hi ranked $(grep -c RANK s63_rk/$c.out) end=$(tail -1 s63_rk/$c.out | cut -c1-24)"
fi
