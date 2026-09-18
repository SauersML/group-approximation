#!/bin/sh
# the two (5,3) survivors of the pipeline, 50_30 #258 and #470: larger finiteness cap, then R8s4 SAT on both solvers
cd "$(dirname "$0")"
nice -n 10 timeout 1200 python3 bigcap.py census_50_30.json 60000 258 470 >> bigcap5030.log 2>&1; echo "cap exit=$?" >> bigcap5030.log
for i in 258 470; do
  nice -n 10 timeout 1200 python3 bigsat.py census_50_30.json $i 8 4 >> bigsat5030.log 2>&1; echo "R8s4 $i exit=$?" >> bigsat5030.log
done
echo FIN >> bigsat5030.log
