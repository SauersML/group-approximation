#!/bin/bash -l
#SBATCH -J zds-ladder
#SBATCH -p agsmall
#SBATCH -t 01:00:00
#SBATCH --mem=2G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/zds/search/ladder.%j.log
# zds v3 (greedy vertex order): n = 6..16, inner coset limits at n = 14, and the n = 14 survivors
# without the power sieve compared with those of the first version (surv14.txt).
cd /scratch.global/sauer354/zds/search || exit 1
cp /projects/standard/hsiehph/sauer354/zds-search/zds3.c zds3f.c || exit 1
gcc -O2 -std=gnu99 -Wall -o zds3f zds3f.c || { echo "compile failed"; exit 1; }
md5sum zds3f.c "$0" g6.g6 g8.g6 g10.g6 g12.g6 g14.g6 g16.g6 surv14.txt
run() {
  name=$1; shift; t0=$(date +%s)
  ./zds3f "$@" > $name.out 2> $name.err; rc=$?
  echo "== $name: zds3f $* rc=$rc seconds=$(( $(date +%s) - t0 )) graphs=$(grep -c '^GRAPH' $name.out) surv=$(grep -c '^SURV' $name.out) budget=$(grep -c BUDGET $name.out)"
  tail -1 $name.out; head -2 $name.err
}
B="-c 1000 -cl 64000 -pw 4 8"
for n in 6 8 10 12 14 16; do run L$n $B < g$n.g6; done
for c in 0 250; do run L14-c$c -c $c -cl 64000 -pw 4 8 < g14.g6; done
run L14-nopw -c 1000 -cl 64000 < g14.g6
ports() {
  awk '$1 == "SURV" { s = $2; p = 0
    for (i = 3; i <= NF && $i != "rels"; i++) { if (p) s = s " " $i; if ($i == "ports") p = 1 }
    print s }' "$1" | sort
}
ports surv14.txt > surv14.ports; ports L14-nopw.out > L14-nopw.ports
echo "n=14 without power sieve: v1 survivors $(wc -l < surv14.ports), v3 survivors $(wc -l < L14-nopw.ports), common $(comm -12 surv14.ports L14-nopw.ports | wc -l)"
for n in 12 14 16; do
  grep '^GRAPH' L$n.out | awk '{ print $5 }' | sort -n |
    awk -v n=$n '{ a[NR] = $1; t += $1 } END { print "n=" n, "graphs", NR, "nodes", t, "per graph", t / NR, "median", a[int(NR / 2)], "max", a[NR] }'
done
echo ALLDONE
