#!/usr/bin/env bash
# Pass 1 of the 3x6 census: gapcensus.py over the 68,844 survivors of `enumtables6 3 6 prune`, in resumable chunks.
# Usage: pass1.sh REPS WORKDIR   (C = experiments/gottschalk-residual-gap-census-2026-09-17)
set -u
REPS="$1"; WD="$2"; C="${C:-$(cd "$(dirname "$0")/../gottschalk-residual-gap-census-2026-09-17" && pwd)}"
N=$(wc -l < "$REPS"); STEP=4000
mkdir -p "$WD"
a=0; k=0
while [ "$a" -lt "$N" ]; do
  b=$((a + STEP)); [ "$b" -gt "$N" ] && b=$N
  out="$WD/r36_$(printf %03d $k).jsonl"
  nice -n 10 timeout 1200 python3 "$C/gapcensus.py" reps 3 6 "$REPS" 5 200 "$out" "$a" "$b" >> "$WD/pass1.log" 2>&1
  done_to=$(tail -n 1 "$out" 2>/dev/null | python3 -c 'import sys,json; l=sys.stdin.read().strip(); print(json.loads(l)["id"]+1 if l else -1)' 2>/dev/null || echo -1)
  if [ "$done_to" -lt "$b" ]; then
    echo "chunk $k stopped at $done_to of $a..$b" >> "$WD/pass1.log"
    [ "$done_to" -le "$a" ] && { echo "no progress, abort" >> "$WD/pass1.log"; exit 1; }
    a=$done_to
  else
    a=$b
  fi
  k=$((k + 1))
done
echo "pass1 done" >> "$WD/pass1.log"
