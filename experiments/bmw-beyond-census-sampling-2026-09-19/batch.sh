#!/bin/bash
# batch.sh: 8 patterns beyond the census degrees, seeds 100..(100+N-1), one sample per process (<=1200 s)
S=/tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad
cd $(dirname $0); export TMPD=$S/w13tmp; N=${N:-8}
for p in "5 0 4 0" "6 0 3 0" "5 0 5 0" "5 1 4 1" "6 1 3 1" "5 2 4 2" "6 3 3 1" "5 2 5 2"; do
  for j in $(seq 0 $((N-1))); do
    nice -n 10 timeout 1200 python3 sample.py $p $((100+j)) 1 batch.jsonl || echo "TIMEOUT $p seed $((100+j))" >> batch.err
  done
done
echo BATCH-DONE >> batch.err
