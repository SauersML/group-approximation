#!/bin/bash
# ./stageseg.sh SEGDIR EXPDIR : collect the finished stages k<X>_<i>.txt of the four block chains run by segchain.sh in
# SEGDIR, check that they are K lines only at points of the block T<X>.txt, gzip them to EXPDIR/segments/ and print a table
W=$(cd "${1:?segment dir}" && pwd); E=$(cd "${2:?experiment dir}" && pwd)
cd "$W" || exit 1; mkdir -p $E/segments
for X in A B C D; do
  : > seg$X.cat; n=0
  for i in $(seq 1 99); do
    grep -q "seg $X stage $i:" seg$X.log 2>/dev/null || break
    [ -s k${X}_$i.txt ] || break
    cat k${X}_$i.txt >> seg$X.cat; n=$i
  done
  L=$(wc -l < seg$X.cat); D=$(grep -c '^D' seg$X.cat)
  # every deleted point must be in T_X (K only, no D): check
  out=$(awk '{s=""; for(i=2;i<=9;i++) s=s $i " "; print s}' seg$X.cat | sed 's/ *$//' | LC_ALL=C sort > del$X.txt; sed 's/ *$//' T$X.txt | LC_ALL=C sort > tx$X.txt; LC_ALL=C comm -23 del$X.txt tx$X.txt | wc -l)
  gzip -9n < seg$X.cat > $E/segments/k-seg$X-8-10.txt.gz
  echo "$X stages=$n lines=$L D=$D outsideTX=$out left_in_TX=$(( $(wc -l < T$X.txt) - L )) sha=$(sha256sum < $E/segments/k-seg$X-8-10.txt.gz | cut -c1-64)"
  rm -f del$X.txt tx$X.txt
done
cp TA.txt TB.txt TC.txt TD.txt $E/segments/ && gzip -9nf $E/segments/T?.txt
