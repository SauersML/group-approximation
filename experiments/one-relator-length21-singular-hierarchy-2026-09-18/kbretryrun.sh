#!/bin/sh
# Run kbretry.sh (a<->t renamed) over chunk files, each under a 1200 s cap; noclobber claims.
for c in "$@"; do
  ( set -C; : > kbr_$c.out ) 2>/dev/null || continue
  nice -n 10 timeout 1200 sh kbretry.sh $c 120 > kbr_$c.out 2>&1
done
