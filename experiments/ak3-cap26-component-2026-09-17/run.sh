#!/bin/bash
# run.sh RANK CAP MAXSTATES NAME: S_CAP of AK(3) in rank RANK by capbfs, in slots under
# nice -n 10 timeout 1200 (capbfs ends each slot after 1100 s with exit 7).  Log NAME.log,
# checkpoint NAME.ck, final dump NAME.ck.txt.  The runs of this directory were
#   run.sh 2 26 33000000 c26   (rank2-cap26.log)
#   run.sh 3 26 20000000 r3c26 (rank3-cap26.log)
#   run.sh 3 24 4000000 r3c24  (rank3-cap24.log)
#   BUDGET=60 run.sh 2 24 4000000 c24 (calib.log: 60 s slots)
R=$1 C=$2 M=$3 N=$4
if [ -f $N.ck ]; then nice -n 10 timeout 1200 ./capbfs resume $N.ck >> $N.log; ex=$?
else nice -n 10 timeout 1200 ./capbfs $R $C $M xxxYYYY xyxYXY $N.ck > $N.log; ex=$?; fi
while [ $ex -eq 7 ]; do nice -n 10 timeout 1200 ./capbfs resume $N.ck >> $N.log; ex=$?; done
echo "FINAL exit $ex" >> $N.log
