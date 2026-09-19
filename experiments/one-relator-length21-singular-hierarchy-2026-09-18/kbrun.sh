#!/bin/sh
# Run kbhyp.sh over chunk files given as args, each chunk under its own 1200 s cap.  A chunk is
# claimed by creating its output file (noclobber), so several streams can share one list.
K=/tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/sw104-build/kbmag/bin/x86
for c in "$@"; do
  ( set -C; : > kb_$c.out ) 2>/dev/null || continue
  nice -n 10 timeout 1200 sh ../one-relator-top-magnus-intersection-2026-09-18/kbhyp.sh $K $c 120 > kb_$c.out 2>&1
done
