#!/bin/bash
# usage: runcaps.sh RANK caps...
R=$1; shift
for c in "$@"; do
  echo "== tbfs $R $c AK(3) tunnels on"
  s=$(date +%s)
  nice -n 10 timeout 1200 ./tbfs $R $c 20000000 xxxYYYY xyxYXY | grep -v "^depth"
  echo "exit $? time $(( $(date +%s) - s ))s"
done
echo ALLDONE
