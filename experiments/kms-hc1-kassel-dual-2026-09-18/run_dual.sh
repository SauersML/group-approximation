#!/bin/sh
# the three edge S-pair jumps at (p,p,p), for the three p-map choices alpha, with t-parts stored in M = u(N)/u(N)H^+
# usage: sh run_dual.sh p   (from this directory; writes to stdout)
# pairs.out: SEEDS=1 PAIRTAB=1 ./fo_dual p p 1 p aA aB > tables; python3 syz_eval.py p t00 t10 t01; SEEDFORM=1 ./fo_dual p p 1 p aA aB
p=$1
g++ -O2 -std=c++17 -o fo_dual fo_dual.cpp || exit 1
for sl in "$p 1 $p" "1 $p $p" "$p $p 1"; do for al in "0 0" "1 0" "0 1"; do
  echo "== slice $sl alpha $al"
  s=$(date +%s)
  nice -n 10 timeout 1200 ./fo_dual $p $sl $al | grep -E "^p=|JUMP|SANITY|WARN|SUMMARY"
  echo "   time $(( $(date +%s) - s ))s"
done; done
