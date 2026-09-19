#!/bin/bash
# analyze63.sh -- after the 72 sub-slices of the 6+6/3 symmetric scan: dedupe candidates by frontier signature,
# rank by per-type overhead growth (single scanned start), and run the return-time test on the bounded ones.
# Lane gq-nv-obstruct, 2026-09-18. MSI only; single core; stage argument selects one step (each <= 10 min).
set -u
cd /projects/standard/hsiehph/sauer354/gqsrc/gq-nv-obstruct
case "$1" in
  dedupe)
    cat s63/*.out | grep '^PASS' | awk '{ sig=$0; sub(/.*t:/, "", sig); if (!(sig in seen)) { seen[sig]=1; print } }' > s63_uniq.txt
    echo "unique candidates: $(wc -l < s63_uniq.txt)"
    echo "scan totals: $(grep -h '^scan' s63/*.out | awk '{split($5,a,"="); split($6,b,"="); t+=a[2]; c+=b[2]} END {print "tried=" t, "cand=" c}')";;
  rank)
    timeout 580 ./rtm_levels_one 6 3 300000 < s63_uniq.txt > s63_rank.out
    echo "ranked: $(grep -c RANK s63_rank.out) done=$(tail -1 s63_rank.out)"
    grep RANK s63_rank.out | awk '{split($2,a,"="); split($3,b,"="); print "growth=" a[2]-b[2]}' | sort | uniq -c | sort -t= -k2 -n | head -8;;
  recur)
    grep RANK s63_rank.out | awk '{split($2,a,"="); split($3,b,"="); if (a[2]-b[2] <= 0) print}' > s63_bounded.txt
    echo "bounded (growth <= 0): $(wc -l < s63_bounded.txt)"
    i=0; S=$(date +%s)
    while read -r line; do
      i=$((i+1)); [ $(( $(date +%s) - S )) -gt 500 ] && { echo "time cap after $i"; break; }
      B=$(echo "$line" | sed 's/.*beta=\([0-9,]*\).*/\1/'); ST=$(echo "$line" | sed 's/.*start=\([0-9]*\).*/\1/')
      d=s63_rec/$i; mkdir -p $d; cd $d
      timeout 40 ../../rtm_cert 6 3 21 $B $ST 0 400000 8 1 0 3 > cert.out 2>&1
      NY=$(wc -l < yt.txt 2>/dev/null || echo 0)
      REC=$(timeout 40 ../../rtm_recur 6 3 21 $B $ST 0 4000000 10 10 2 6 | grep '^return' | awk '{print $3}' | sed 's/n=//' | tr '\n' ' ')
      M8=$(for x in $REC; do echo $((x % 8)); done | sort -u | tr '\n' ',')
      echo "machine $i beta=$B start=$ST Ytypes=$NY returns_n=[$REC] n_mod8={$M8}"
      cd ../..
    done < s63_bounded.txt;;
esac
echo ANALYZE63_DONE
