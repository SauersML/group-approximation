#!/bin/bash
# re-run the timed-out rank-3 chunk 240000..270000 in two halves, after sweep.sh finishes
while pgrep -f 'sweep.sh 3' >/dev/null; do sleep 15; done
for lo in 240000 255000; do
  hi=$((lo+15000)); s=$(date +%s)
  nice -n 10 timeout 1200 ./tunnel 3 24 0 s24r3.txt $lo $hi > sw_3_$lo.out
  echo "chunk $lo..$hi exit $? time $(( $(date +%s) - s ))s"
  grep -v "^NEW" sw_3_$lo.out
  grep "^NEW" sw_3_$lo.out | sed "s/.*-> //" | sort -u > sw_3_$lo.new; rm sw_3_$lo.out
done
echo RESWEEPDONE
