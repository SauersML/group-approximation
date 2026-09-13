#!/bin/bash -l
#SBATCH -J zds-test
#SBATCH -p agsmall
#SBATCH -t 02:00:00
#SBATCH --mem=4G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/zds/search/test.%j.log
# Soundness tests for zds on structures realized in finite groups, then the search on n = 6..14.
SIF=/common/software/install/bundle/images/registry.msi.umn.edu/shpc_module_library/sagemath/10.7/registry.msi.umn.edu-shpc_module_library-sagemath-10.7-sha256:ea6b3bd2762c322e36841aaffe64ecad83d8969a2576d2b5165f79af3bbcdd17.sif
module load singularity 2>/dev/null
cd /scratch.global/sauer354/zds/search || exit 1
md5sum zds.c testgen.g
singularity exec -B /common,/scratch.global,/projects,/home "$SIF" gap -q testgen.g < /dev/null > testgen.out 2>&1
echo "GAP rc=$?"; tail -3 testgen.out; wc -l testdata.txt
for c in 0 64 4000; do
  echo "== test c=$c"; ./zds -t -c $c < testdata.txt > test-c$c.out 2>&1; echo "rc=$?"; tail -2 test-c$c.out
done
for n in 6 8 10 12 14; do
  singularity exec -B /common,/scratch.global "$SIF" nauty-geng -c -t -d3 -D3 $n g$n.g6 2> g$n.geng.txt
  echo "== n=$n graphs $(wc -l < g$n.g6)"
  t0=$(date +%s)
  timeout 1800 ./zds -c 4000 < g$n.g6 > s$n.out 2> s$n.err; rc=$?
  echo "rc=$rc seconds=$(( $(date +%s) - t0 )) surv_lines=$(grep -c '^SURV' s$n.out)"; tail -1 s$n.out
done
echo ALLDONE
