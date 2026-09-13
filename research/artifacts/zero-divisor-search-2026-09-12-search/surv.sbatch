#!/bin/bash -l
#SBATCH -J zds-surv
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/zds/search/surv.%j.log
# GAP analysis of the n = 14 survivors, then the revised zds: soundness, DFS control, n = 14 again.
SIF=/common/software/install/bundle/images/registry.msi.umn.edu/shpc_module_library/sagemath/10.7/registry.msi.umn.edu-shpc_module_library-sagemath-10.7-sha256:ea6b3bd2762c322e36841aaffe64ecad83d8969a2576d2b5165f79af3bbcdd17.sif
module load singularity 2>/dev/null
cd /scratch.global/sauer354/zds/search || exit 1
cp /projects/standard/hsiehph/sauer354/zds-search/zds.c /projects/standard/hsiehph/sauer354/zds-search/surv.g . || exit 1
md5sum zds.c surv.g surv14.txt testdata.txt g14.g6
awk 'BEGIN { print "ZdsSurv := [" }
  { r = 0; s = ""
    for (i = 1; i <= NF; i++) { if ($i == "cosets") break; if (r) s = s (s == "" ? "" : ", ") "\"" $i "\""; if ($i == "rels") r = 1 }
    printf "%s[ %s ]\n", (NR > 1 ? ", " : "  "), s }
  END { print "];" }' surv14.txt > surv14.g
t0=$(date +%s)
timeout 5400 singularity exec -B /common,/scratch.global,/projects,/home "$SIF" gap -q -o 6g surv.g < /dev/null > surv14.gap.out 2>&1
echo "== GAP rc=$? seconds=$(( $(date +%s) - t0 ))"; cat surv14.gap.out
gcc -O2 -std=gnu99 -Wall -o zds2 zds.c || { echo "compile failed"; exit 1; }
run() {
  name=$1; shift; t0=$(date +%s)
  ./zds2 "$@" > $name.out 2> $name.err; rc=$?
  echo "== $name: zds2 $* rc=$rc seconds=$(( $(date +%s) - t0 )) bad=$(grep -c -E '^(FAIL|CONTROL)' $name.out) surv=$(grep -c '^SURV' $name.out)"
  tail -1 $name.out; head -3 $name.err
}
run v2-t-c0 -t -c 0 < testdata.txt
run v2-t-c4000 -t -c 4000 -cl 64000 < testdata.txt
run v2-ctl-c4000 -t2 -c 4000 -cl 64000 < testdata.txt
run v2-s14 -c 4000 -cl 64000 -pw 4 8 < g14.g6
grep '^SURV' v2-s14.out | cut -c1-160
echo ALLDONE
