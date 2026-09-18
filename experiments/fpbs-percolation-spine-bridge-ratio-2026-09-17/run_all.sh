#!/bin/sh
# Grid of Br/TJT runs.  usage: run_all.sh <brratio-binary> <outdir>
# Each job: nice -n 10 timeout 1200, single-threaded; finished outputs are skipped on restart.
B=$1; O=$2; mkdir -p $O
job() { # type n h pp r M envs K tag
  f=$O/$9.out; [ -s $f ] && return
  nice -n 10 timeout 1200 $B $1 $2 $3 $4 $5 $6 $7 $8 20 $(echo $9 | cksum | cut -d' ' -f1) > $f.tmp && mv $f.tmp $f
}
for r in 0.3 0.6; do
 # supercritical infinite-cluster spines (margin M >> xi)
 for spec in "0.52 300" "0.55 150" "0.6 100" "0.7 60" "0.85 40"; do
  set -- $spec; pp=$1; M=$2
  for n in 1 2 4 8 16 32 64 128 256; do job 0 $n 0 $pp $r $M 400 20 path_p${pp}_r${r}_n$n; done
 done
 # critical proxies: clusters reaching distance M (density -> 0 as M grows)
 for M in 10 40 160 640; do
  for n in 1 2 4 8 16 32 64 128; do job 0 $n 0 0.5 $r $M 400 20 crit_M${M}_r${r}_n$n; done
 done
 # two parallel routes (rectangle boundary)
 for spec in "0.55 150" "0.7 60" "0.5 160"; do
  set -- $spec; pp=$1; M=$2
  for n in 8 32 128; do for h in 2 8 32; do job 1 $n $h $pp $r $M 200 10 rect_p${pp}_M${M}_r${r}_n${n}_h$h; done; done
 done
done
echo done > $O/ALLDONE
