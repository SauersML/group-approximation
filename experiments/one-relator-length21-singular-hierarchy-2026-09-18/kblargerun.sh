#!/bin/sh
# Run kbhyp2.sh (autgroup -large, SWAP=$SWAP) over chunk files, 1200 s cap each; noclobber claims.
K=/tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/sw104-build/kbmag/bin/x86
for c in "$@"; do
  ( set -C; : > kb2_${c}_s$SWAP.out ) 2>/dev/null || continue
  AUTOPT=-large nice -n 10 timeout 1200 sh kbhyp2.sh $K $c ${LIM:-240} > kb2_${c}_s$SWAP.out 2>&1
done
