#!/bin/bash
# Remote, run detached on MSI: snapshot census job 753122, run census_compare.py on the degrees complete in
# every shard, and leave compare_done.txt as the sentinel.
cd /scratch.global/sauer354/hl-f-kernel-profiles || exit 1
rm -f compare_done.txt
md5sum census_compare.py kprof.c census_shard.sh census.sbatch > compare_md5.txt
sacct -j 753122 -X --format=JobID,State,ExitCode,Elapsed -n > census_sacct_snapshot.txt 2>&1
date >> census_sacct_snapshot.txt
for f in logs/census_753122_*.log; do
  echo "$(basename "$f") $(grep -h '^K ' "$f" | tr '\n' ';') $(grep -h '^k=' "$f" | tr '\n' ';')"
done > census_progress_snapshot.txt
/usr/bin/python3.12 census_compare.py > census_compare.out 2>&1
echo "COMPARE_RC=$?" >> census_compare.out
echo DONE > compare_done.txt
