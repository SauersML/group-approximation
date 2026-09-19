#!/bin/bash
# Replay with kzc1 the (8,10) middle-piece stages found by kzs3 (E2-E4, F2-F4), in chunks of 12 lines.
# Needs O.txt (sets/O-8-10.txt.gz of the (8,10) directory, in its order), km.txt (chains/k-middle-8-10.txt.gz,
# uncompressed) and ./kzc1.  After each stage the end set is compared with the sorted start set of the next stage
# (sha256 prefix from chains/stage-index.txt).  Log: kzc1-stages.log.
cd "${1:-.}"; LOG=kzc1-stages.log
run(){ # name first last next_sha16
  st=$1; a=$2; b=$3
  for ((f=a; f<=b; f+=12)); do l=$((f+11)); [ $l -gt $b ] && l=$b
    grep -q "^$st $f $l ACCEPT" $LOG 2>/dev/null && continue
    out=$(nice -n 10 timeout 1200 ./kzc1 8 10 O.txt km.txt $f $l end_$st.txt); c=$?
    echo "$st $f $l $([ $c = 0 ] && echo ACCEPT || echo "EXIT $c") $out" >> $LOG; [ $c = 0 ] || exit 1; done
  h=$(LC_ALL=C sort end_$st.txt | sha256sum | cut -c1-16)
  echo "$st end set: $(wc -l < end_$st.txt) points, sorted sha256 $h, expected $4 $([ $h = $4 ] && echo MATCH || echo MISMATCH)" >> $LOG; }
run E2 8366 8518 26dd9b7ac2ef3001
run E3 8519 8663 31c080a6c4b1d6a0
run E4 8664 8848 0dbba22f43d66f55
run F2 8905 9025 fab84b06277c00c8
run F3 9026 9336 e8dcefc523f3e94a
run F4 9337 9408 ebb75b77af92f897
echo "ALL DONE" >> $LOG
