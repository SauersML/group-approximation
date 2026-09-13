#!/bin/bash -l
#SBATCH -J zds-surv22
#SBATCH -p agsmall
#SBATCH -t 10:00:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/zds/search/surv22/surv22.%j.log
# n = 22 survivors (job 603988, shards 17 and 52): rerun zds on the two graphs with stronger sound
# sieves (larger leaf coset limit, longer power sieve, BS(1,j) sieve at leaves), then GAP analysis.
SIF=/common/software/install/bundle/images/registry.msi.umn.edu/shpc_module_library/sagemath/10.7/registry.msi.umn.edu-shpc_module_library-sagemath-10.7-sha256:ea6b3bd2762c322e36841aaffe64ecad83d8969a2576d2b5165f79af3bbcdd17.sif
module load singularity 2>/dev/null
cd /scratch.global/sauer354/zds/search/surv22 || exit 1
cp ../n22/zds22.c zds22s.c || exit 1
md5sum zds22s.c surv22.g surv22rels.g g22surv.g6 "$0"
[ "$(md5sum < zds22s.c | cut -c1-32)" = 18a83240ff82d0bcdcdcd33c15780d72 ] || { echo "zds source md5 mismatch"; exit 1; }
sed 's/#define MAXC (1 << 18)/#define MAXC (1 << 22)/' zds22s.c > zdsbig.c
grep -n 'define MAXC' zdsbig.c
gcc -O2 -std=gnu99 -Wall -o zdsbig zdsbig.c || { echo "compile failed"; exit 1; }
run() {
  name=$1; lim=$2; shift 2; t0=$(date +%s)
  timeout $lim ./zdsbig "$@" < g22surv.g6 > $name.out 2> $name.err; rc=$?
  echo "== $name: zdsbig $* rc=$rc seconds=$(( $(date +%s) - t0 )) graphs=$(grep -c '^GRAPH' $name.out) surv=$(grep -c '^SURV' $name.out)"
  grep '^GRAPH' $name.out | cut -c1-200; tail -1 $name.out; head -3 $name.err
}
run r0-repro 3600 -c 1000 -cl 64000 -pw 4 8
run r1-bs 3600 -c 1000 -cl 64000 -pw 4 8 -bs 16 -bsd 0
run r2-big 7200 -c 1000 -cl 1000000 -pw 6 12 -bs 16 -bsd 0
run r3-bigger 14400 -c 1000 -cl 4000000 -pw 8 16 -bs 32 -bsd 0
grep '^SURV' r3-bigger.out | cut -c1-120
t0=$(date +%s)
timeout 7200 singularity exec -B /common,/scratch.global,/projects,/home "$SIF" gap -q -o 7g surv22.g < /dev/null > surv22.gap.out 2>&1
echo "== GAP rc=$? seconds=$(( $(date +%s) - t0 ))"; cat surv22.gap.out
echo ALLDONE
