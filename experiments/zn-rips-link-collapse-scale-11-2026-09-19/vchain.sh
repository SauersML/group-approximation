#!/bin/bash
# Replay the (8,11) (D) prefix with vcert2 in 25,000-line chunks; each chunk starts from the state of the previous one.
cd "$(dirname "$0")"; LOG=vchain.log
prev=""; for c in vp/ch*; do b=${c##*/}
  if grep -q "^$b OK" $LOG 2>/dev/null; then prev=vp/st-$b; continue; fi
  if [ -z "$prev" ]; then a=""; else a="-i $prev"; fi
  nice -n 10 timeout 1200 ./vcert2 8 11 $a -o vp/st-$b $c > vp/out 2>&1; code=$?; out=$(tail -1 vp/out)
  if [ $code = 0 ] || [ $code = 2 ]; then echo "$b OK exit $code $out" >> $LOG; else echo "$b FAIL exit $code $out" >> $LOG; exit 1; fi
  [ -n "$prev" ] && rm -f $prev; prev=vp/st-$b; done
nm(){ sed 's/ *$//' "$1" | grep -v '^$' | LC_ALL=C sort; }
cmp -s <(nm $prev) <(nm o6.txt) && echo "PREFIX VERIFIED: end set = o6 ($(wc -l < o6.txt) points)" >> $LOG || echo "PREFIX END MISMATCH" >> $LOG
