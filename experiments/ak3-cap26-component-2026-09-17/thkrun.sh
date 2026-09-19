#!/bin/bash
# thkrun.sh K NW: worker K of NW runs thkcheck on chunks of new26.txt (CH states each), 1200 s cap per chunk
# run in the directory holding thkcheck and new26.txt; the run used CH=12000 and NW=2
K=$1; NW=$2; CH=${CH:-12000}; N=$(wc -l < new26.txt)
for ((lo=K*CH; lo<N; lo+=NW*CH)); do
  hi=$((lo+CH)); t0=$(date +%s)
  out=$(nice -n 10 timeout 1200 ./thkcheck 2 new26.txt $lo $hi); ex=$?
  echo "chunk $lo exit $ex time $(( $(date +%s)-t0 ))s $out" >> thk26.log
done
echo "WORKER $K DONE" >> thk26.log
