#!/usr/bin/env bash
# Chunked lower exponent-p central tower of Gamma^A2_p with the standalone ANU pq.
# Each chunk is one pq process under `nice -n 10 timeout 1200`: it restores the last
# saved class, computes next classes one at a time and saves after each one.
# Usage: pqchunk.sh <pq binary> <p> <target class> <workdir>
# Log: <workdir>/tower.log gets one line "class k order p^m" per class.
set -u
pq=$1; p=$2; target=$3; W=$4; mkdir -p "$W"; cd "$W" || exit 1
REL="{a^$p, b^$p, c^$p, [a,b,a], [a,b,b], [b,c,b], [b,c,c], [a,c,a], [a,c,c]}"
last() { ls save_* 2>/dev/null | sed 's/save_//' | sort -n | tail -1; }
while :; do
  k=$(last)
  if [ -z "$k" ]; then   # first chunk: compute to class 20 from the presentation
    printf '1\nG\n%s\n20\n1\n{a, b, c}\n%s\n0\n\n2\nsave_20\n0\n' "$p" "$REL" > in.txt
  else
    [ "$k" -ge "$target" ] && { echo "DONE $k" >> tower.log; exit 0; }
    { printf '3\nsave_%s\n' "$k"
      for c in $(seq $((k+1)) "$target"); do printf '6\n2\nsave_%s\n' "$c"; done
      printf '0\n'; } > in.txt
  fi
  nice -n 10 timeout 1200 "$pq" -s 200000000 < in.txt > chunk.out 2>&1
  grep -E 'has order|took' chunk.out >> tower.log
  k2=$(last)
  # keep only the newest two save files
  for f in $(ls save_* | sed 's/save_//' | sort -n | head -n -2); do rm -f "save_$f"; done
  [ "$k2" = "$k" ] && { echo "NO PROGRESS at $k" >> tower.log; exit 2; }
done
