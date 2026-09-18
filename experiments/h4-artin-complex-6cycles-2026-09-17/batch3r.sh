#!/bin/sh
# resume after container restart (chunks 0-5 done)
for i in $(seq 6 35); do
  A0=$i A1=$((i+1)) nice -n 10 timeout 1200 ./tsearch data/H4_22222 4 5 2>>batch3.err >> H4_22222.out
  echo "chunk $i exit $?" >> batch3.err
done
echo done > batch3.done
