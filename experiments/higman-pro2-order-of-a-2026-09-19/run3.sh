#!/bin/sh
# usage: run3.sh NAME KEEP SEED MAXCL 'EXTRA-list' [RESTARTS]
# checkpointed: each GAP process runs under nice -n 10 timeout 1200; on timeout it resumes from NAME.ws
cd "$(dirname "$0")"
nice -n 10 timeout 1200 gap -q -o 2g -c "EXTRA:=function(a,b,c,d) return $5; end;; KEEP:=$2;; SEED:=$3;; MAXCL:=$4;; NAME:=\"$1\";; CKPT:=true;;" grow2.g >> $1.out 2>&1
rc=$?; i=0
while [ $rc = 124 ] && [ -f $1.ws ] && [ $i -lt ${6:-6} ]; do
  echo "resume $i" >> $1.out
  nice -n 10 timeout 1200 gap -q -o 2g -L $1.ws loop2.g >> $1.out 2>&1; rc=$?; i=$((i+1))
done
echo "exit $rc" >> $1.out
