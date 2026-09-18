#!/bin/bash
# usage: sweep.sh RANK DUMP N CHUNK -> one tunnel step from every state of the cap-24 dump
R=$1; D=$2; N=$3; C=$4
for ((lo=0; lo<N; lo+=C)); do
  hi=$((lo+C)); s=$(date +%s)
  nice -n 10 timeout 1200 ./tunnel $R 24 0 $D $lo $hi > sw_${R}_$lo.out
  echo "chunk $lo..$hi exit $? time $(( $(date +%s) - s ))s"
  grep -v "^NEW" sw_${R}_$lo.out
  grep "^NEW" sw_${R}_$lo.out | sed "s/.*-> //" | sort -u > sw_${R}_$lo.new; rm sw_${R}_$lo.out
done
echo SWEEPDONE
