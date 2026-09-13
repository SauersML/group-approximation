#!/bin/bash -l
#SBATCH -J zds-pwdbg
#SBATCH -p agsmall
#SBATCH -t 01:00:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/zds/search/surv22/pwdbg.%j.log
# n = 22 survivors: print-only debug variant of zds3.c (MAXC 2^22, prints each leaf excluded by the power
# sieve with its power roots and edge products), then GAP recomputes each quotient independently.
SIF=/common/software/install/bundle/images/registry.msi.umn.edu/shpc_module_library/sagemath/10.7/registry.msi.umn.edu-shpc_module_library-sagemath-10.7-sha256:ea6b3bd2762c322e36841aaffe64ecad83d8969a2576d2b5165f79af3bbcdd17.sif
module load singularity 2>/dev/null
cd /scratch.global/sauer354/zds/search/surv22 || exit 1
md5sum zdsdbg.c pwcheck.g g22surv.g6 "$0"
gcc -O2 -std=gnu99 -Wall -o zdsdbg zdsdbg.c || { echo "compile failed"; exit 1; }
t0=$(date +%s)
timeout 1800 ./zdsdbg -c 1000 -cl 1000000 -pw 6 12 < g22surv.g6 > pwdbg.out 2> pwdbg.err; rc=$?
echo "== pwdbg rc=$rc seconds=$(( $(date +%s) - t0 )) excluded=$(grep -c '^PWPRUNE' pwdbg.out) surv=$(grep -c '^SURV' pwdbg.out)"
tail -1 pwdbg.out; head -3 pwdbg.err
awk 'BEGIN { print "ZdsPw := [" }
  /^PWPRUNE/ { mode = ""; c = ""; p = ""; w = ""
    for (i = 1; i <= NF; i++) {
      if ($i == "rels" || $i == "pw" || $i == "edges" || $i == "cosets") { mode = $i; continue }
      if (mode == "rels") c = c (c == "" ? "" : ", ") "\"" $i "\""
      else if (mode == "pw") { split($i, a, "\\^"); p = p (p == "" ? "" : ", ") "[\"" a[1] "\", " a[2] "]" }
      else if (mode == "edges") w = w (w == "" ? "" : ", ") "\"" $i "\""
    }
    printf "%s[ [ %s ], [ %s ], [ %s ] ]\n", (k++ > 0 ? ", " : "  "), c, p, w }
  END { print "];" }' pwdbg.out > pwprune.g
grep -c '^\(  \|, \)\[' pwprune.g
t0=$(date +%s)
timeout 2400 singularity exec -B /common,/scratch.global,/projects,/home "$SIF" gap -q -o 7g pwcheck.g < /dev/null > pwcheck.gap.out 2>&1
echo "== GAP rc=$? seconds=$(( $(date +%s) - t0 ))"; cat pwcheck.gap.out
echo ALLDONE
