#!/bin/sh
# usage: run2.sh NAME KEEP SEED MAXCL 'EXTRA-list' [PRIO]
cd "$(dirname "$0")"
P=${6:-[1,2,3,4]}
nice -n 10 timeout ${TMO:-1200} gap -q -o 2g -c "EXTRA:=function(a,b,c,d) return $5; end;; KEEP:=$2;; SEED:=$3;; MAXCL:=$4;; NAME:=\"$1\";; PRIO:=$P;;" grow2.g > $1.out 2>&1
echo "exit $?" >> $1.out
