#!/bin/bash
# ./assemble.sh OUTDIR : writes OUTDIR/k-middle-8-10.txt.gz, blocks-8-10.txt.gz, stage-index.txt from the stage files,
# checking that every chain's lines are at points of its block, the stages chain exactly and the end set is O \ T
cd "$(dirname "$0")" || exit 1; out=$1; mkdir -p $out; : > mid.txt; : > $out/stage-index.txt; : > blocks.tmp
nm(){ sed 's/ *$//' "$1" | grep -v '^$' | LC_ALL=C sort; }
V6=/tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/w8-103/verify.log
V7=../verify7.log; fail=0; line=0
nm sA_0.txt > cur.srt
printf '# chain stage first_line last_line search start_size sha256(sorted start set) replay\n' >> $out/stage-index.txt
for X in A B E F C D; do
  n=$(ls k${X}_*.txt | sed "s/k${X}_\([0-9]*\).txt/\1/" | sort -n | tail -n 1)
  # the block: points of this chain's lines (checked against T?.txt / Bleft halves)
  case $X in B) blk=TBp.txt; LC_ALL=C comm -23 <(nm TB.txt) <(nm Bleft.txt) > TBp.txt;; *) blk=T$X.txt;; esac
  nm s${X}_0.txt | cmp -s - cur.srt || { echo "JOIN FAIL before $X"; fail=1; }
  for i in $(seq 1 $n); do
    c=$(wc -l < k${X}_$i.txt); a=$((line+1)); line=$((line+c))
    grep -c -v '^K ' k${X}_$i.txt | grep -q '^0$' || { echo "non-K line in $X$i"; fail=1; }
    srch=kzs2; { [ $X = E ] || [ $X = F ]; } && [ $i -ge 2 ] && srch=kzs3
    sz=$(wc -l < cur.srt); sh=$(sha256sum cur.srt | cut -c1-16)
    tier=search
    grep -q "^$X$i VERIFIED" $V6 && tier=kzv6; grep -q "^$X$i VERIFIED" $V7 && { [ $tier = kzv6 ] && tier=kzv6+kzv7 || tier=kzv7; }
    printf '%s %d %d %d %s %d %s %s\n' $X $i $a $line $srch $sz $sh $tier >> $out/stage-index.txt
    awk '{k=$2;for(j=3;j<=9;j++)k=k" "$j;print k}' k${X}_$i.txt | LC_ALL=C sort > del.srt
    [ $(LC_ALL=C comm -12 del.srt cur.srt | wc -l) = $c ] || { echo "$X$i deletes absent points"; fail=1; }
    LC_ALL=C comm -23 cur.srt del.srt > cur.t; mv cur.t cur.srt
    nm s${X}_$i.txt | cmp -s - cur.srt || { echo "$X$i end set differs from s${X}_$i"; fail=1; }
    cat k${X}_$i.txt >> mid.txt; sed "s/^/$X /" del.srt >> blocks.tmp
  done
  k=$(grep -c "^$X " blocks.tmp); b=$(wc -l < $blk)
  [ "$(grep "^$X " blocks.tmp | cut -c3- | LC_ALL=C sort)" = "$(nm $blk)" ] && echo "chain $X: $k lines = block ($b points)" || { echo "chain $X: lines are not its block"; fail=1; }
done
nm OminusT.txt | cmp -s - cur.srt && echo "END = O minus T ($(wc -l < cur.srt) points)" || { echo "END differs from O minus T"; fail=1; }
cat TA.txt TB.txt TC.txt TD.txt > Tall.tmp
if cut -c3- blocks.tmp | LC_ALL=C sort | cmp -s - <(nm Tall.tmp) && [ $(wc -l < blocks.tmp) = 18816 ]; then echo "blocks partition T (18816 points)"
else echo "blocks do not partition T"; fail=1; fi; rm -f Tall.tmp
echo "total lines $line"; gzip -9n < mid.txt > $out/k-middle-8-10.txt.gz; gzip -9n < blocks.tmp > $out/blocks-8-10.txt.gz
rm -f mid.txt blocks.tmp cur.srt del.srt TBp.txt; exit $fail
