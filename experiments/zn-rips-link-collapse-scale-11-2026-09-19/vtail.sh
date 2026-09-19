#!/bin/bash
# Replay the (8,11) (D) tail (from O \ T11) with vcert2 in 25,000-line chunks; the last chunk must end at {e_8} (exit 0).
cd "$(dirname "$0")"; LOG=vtail.log; prev=OmT.txt
for c in vt/ch*; do b=${c##*/}
  nice -n 10 timeout 1200 ./vcert2 8 11 -i $prev -o vt/st-$b $c > vt/out 2>&1; code=$?; out=$(tail -1 vt/out)
  if [ $code = 0 ] || [ $code = 2 ]; then echo "$b OK exit $code $out" >> $LOG; else echo "$b FAIL exit $code $out" >> $LOG; exit 1; fi
  [ $prev != OmT.txt ] && rm -f $prev; prev=vt/st-$b; done
[ $code = 0 ] && echo "TAIL VERIFIED: ends at {e_8}" >> $LOG || echo "TAIL DOES NOT END AT {e_8}" >> $LOG
