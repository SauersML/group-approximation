#!/bin/sh
# usage: run4.sh NAME [RESTARTS] : resume NAME.ws with loop3.g under repeated nice -n 10 timeout 1200 runs
cd "$(dirname "$0")"; i=0; rc=124
while [ $rc = 124 ] && [ -f $1.ws ] && [ $i -lt ${2:-12} ]; do
  echo "resume4 $i $(date -u +%T)" >> $1.out
  nice -n 10 timeout 1200 gap -q -o 2g -L $1.ws loop3.g >> $1.out 2>&1; rc=$?; i=$((i+1))
done
echo "exit $rc" >> $1.out
