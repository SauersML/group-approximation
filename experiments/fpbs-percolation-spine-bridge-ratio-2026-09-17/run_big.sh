#!/bin/sh
# Largest critical proxy (M=2560, 150 environments): extends the theta range of run_all.sh.
# usage: run_big.sh <brratio-binary> <outdir>
B=$1; O=$2; mkdir -p $O
for n in 8 32 128; do
  t=crit_M2560_r0.3_n$n; f=$O/$t.out; [ -s $f ] && continue
  nice -n 10 timeout 1200 $B 0 $n 0 0.5 0.3 2560 150 20 10 $(echo $t | cksum | cut -d' ' -f1) > $f.tmp && mv $f.tmp $f
done
echo done > $O/BIGDONE
