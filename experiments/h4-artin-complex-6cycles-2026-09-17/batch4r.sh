#!/bin/sh
# resume after container restart (chunks 0-49 done)
for i in $(seq 50 68); do
  A0=$i A1=$((i+1)) nice -n 10 timeout 1200 ./tsearch data/PH4_22212 4 5 2>>batch4.err >> PH4_22212.out
  echo "chunk $i exit $?" >> batch4.err
done
echo done > batch4.done
