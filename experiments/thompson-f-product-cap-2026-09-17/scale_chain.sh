#!/bin/sh
# Chain large_m_opt.py over growing M, each run initialised from the previous optimum.
# Usage: scale_chain.sh OUTDIR
D=${1:-.}
H=$(dirname "$0")
prev=""
for e in 11 12 14 16 18 20 22; do
  M=$((1 << e))
  if [ -z "$prev" ]; then
    python3 "$H/large_m_opt.py" $M 32 16 12 "$D/p$e.pt"
  else
    python3 "$H/large_m_opt.py" $M 32 16 12 "$D/p$e.pt" "$prev"
  fi
  prev="$D/p$e.pt"
done
