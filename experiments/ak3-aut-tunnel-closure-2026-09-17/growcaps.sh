#!/bin/bash
# usage: growcaps.sh RANK CAP... -> tunnel-closed component of AK(3) from scratch at each cap
R=$1; shift
echo "XYXyxy XXXXyyy" > ak3seed.txt; : > empty.txt
for C in "$@"; do
  s=$(date +%s); echo "== grow $R $C AK(3) from scratch"
  nice -n 10 timeout 1200 ./grow $R $C empty.txt ak3seed.txt g_${R}_$C.out | grep -v "^  "
  echo "exit ${PIPESTATUS[0]} time $(( $(date +%s) - s ))s"; rm -f g_${R}_$C.out
done
