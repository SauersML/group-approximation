#!/bin/bash
# For each profile P given as "a,b,c,...": restore the class of P to O \ T and run D-only sweeps (kzs2 KZ_DONLY=1)
# in budgeted pieces.  REACHES {e_n} means the class need not be in T.  Log: classtest.log.
cd "$(dirname "$0")"
for P in "$@"; do d=ct-$P; mkdir -p $d
  python3 -c "
import sys
P=tuple(map(int,'$P'.split(',')))
for l in open('T.txt'):
  p=list(map(int,l.split()))
  if tuple(sorted((abs(v) for v in p if v),reverse=True))==P: print(l.strip())" > $d/cls.txt
  cat OmT.txt $d/cls.txt > $d/t0.txt; i=1
  while [ $i -le 12 ]; do
    KZ_DONLY=1 nice -n 10 timeout 1200 ./kzs2 8 11 $d/t$((i-1)).txt $d/t$i.txt - 1100 > $d/log$i.txt 2>&1
    rm -f $d/t$((i-1)).txt; grep -q "time budget" $d/log$i.txt || break; i=$((i+1)); done
  echo "$(date -u +%T) class $P ($(wc -l < $d/cls.txt) pts): $(tail -1 $d/log$i.txt)" >> classtest.log
  grep pass $d/log$i.txt | tail -1 >> classtest.log; rm -f $d/t*.txt; done
echo DONE >> classtest.log
