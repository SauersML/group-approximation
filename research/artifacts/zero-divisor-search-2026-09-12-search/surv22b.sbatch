#!/bin/bash -l
#SBATCH -J zds-surv22b
#SBATCH -p agsmall
#SBATCH -t 01:00:00
#SBATCH --mem=4G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/zds/search/surv22/surv22b.%j.log
# n = 22 survivors: which sieve setting excludes them, with the unmodified n = 22 binary (MAXC 2^18),
# plus a second tree (root 19). Same two graphs as surv22.sbatch.
cd /scratch.global/sauer354/zds/search/surv22 || exit 1
md5sum ../n22/zds22 ../n22/zds22.c g22surv.g6 "$0"
[ "$(md5sum < ../n22/zds22.c | cut -c1-32)" = 18a83240ff82d0bcdcdcd33c15780d72 ] || { echo "zds source md5 mismatch"; exit 1; }
run() {
  name=$1; bin=$2; shift 2; t0=$(date +%s)
  timeout 1500 $bin "$@" < g22surv.g6 > $name.out 2> $name.err; rc=$?
  echo "== $name: $bin $* rc=$rc seconds=$(( $(date +%s) - t0 )) graphs=$(grep -c '^GRAPH' $name.out) surv=$(grep -c '^SURV' $name.out)"
  grep '^GRAPH' $name.out | cut -c1-200; tail -1 $name.out; head -3 $name.err
}
B=../n22/zds22
run p1-pw6-cl64k $B -c 1000 -cl 64000 -pw 6 12
run p2-pw4-cl262k $B -c 1000 -cl 262144 -pw 4 8
run p3-pw6-cl262k $B -c 1000 -cl 262144 -pw 6 12
run p4-pw5-cl64k $B -c 1000 -cl 64000 -pw 5 8
run p5-pw4e12-cl64k $B -c 1000 -cl 64000 -pw 4 12
run p6-big-pw4-cl1M ./zdsbig -c 1000 -cl 1000000 -pw 4 8
run p7-root19-pw4 $B -root 19 -c 1000 -cl 64000 -pw 4 8
run p8-root19-pw6 $B -root 19 -c 1000 -cl 64000 -pw 6 12
echo ALLDONE
