#!/bin/sh
# first-order (Rees t-linear) standard basis runs: the three edge S-pairs landing at (p,p,p), for three p-map choices alpha
# usage: sh run_fo.sh p   (writes fo_p<p>.out)
p=$1
g++ -O2 -std=c++17 -o fo_sb fo_sb.cpp || exit 1
for sl in "$p 1 $p" "1 $p $p" "$p $p 1"; do for al in "0 0" "1 0" "0 1"; do
  echo "== slice $sl alpha $al"
  nice -n 10 timeout 1200 ./fo_sb $p $sl $al | grep -E "^p=|test|JUMP|SANITY|WARN|SUMMARY|^GB"
done; done
