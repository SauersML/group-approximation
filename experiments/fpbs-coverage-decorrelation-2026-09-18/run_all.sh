#!/bin/sh
# usage: sh run_all.sh ./kdecor > results.txt
B=$1
for n in 16 64; do
  $B 0.55 150 $n 4000 11
  $B 0.52 300 $n 1500 12
  $B 0.5 10 $n 100000 13
  $B 0.5 40 $n 40000 14
  $B 0.5 160 $n 6000 15
  $B 0.5 640 $n 600 16
done
