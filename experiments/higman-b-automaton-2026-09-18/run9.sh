#!/bin/sh
# driver: resume levels_ck.py until it finishes (exit 0) or fails
cd "$(dirname "$0")"
for i in $(seq 1 40); do
  (ulimit -v 2600000; nice -n 10 timeout 1200 python3 levels_ck.py 9 5 900) >> lev9.out 2>&1
  rc=$?; echo "run $i rc=$rc $(date -u +%H:%M)" >> lev9.out
  [ $rc = 3 ] || break
done
echo FINISHED >> lev9.out
