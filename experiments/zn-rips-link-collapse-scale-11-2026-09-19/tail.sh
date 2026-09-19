#!/bin/bash
# D-only sweeps (kzs2 KZ_DONLY=1) from OmT.txt = O \ T (sets/O-8-11 minus sets/T-8-11), in budgeted pieces; kzs2 is in experiments/zn-rips-link-collapse-scale-10-2026-09-18: piece i reads t(i-1).txt, writes dt(i).txt, t(i).txt.
cd "$(dirname "$0")"; [ -f t0.txt ] || cp OmT.txt t0.txt
i=1; while [ -f t$i.txt ]; do i=$((i+1)); done
while [ $i -le 30 ]; do
  KZ_DONLY=1 nice -n 10 timeout 1200 ./kzs2 8 11 t$((i-1)).txt t$i.txt dt$i.txt 1100 > tlog$i.txt 2>&1
  echo "$(date -u +%T) piece $i: $(tail -1 tlog$i.txt)" >> tail.log
  grep -q "time budget" tlog$i.txt || break
  i=$((i+1)); done
echo DONE >> tail.log
