#!/usr/bin/env bash
W=$1
while read -r n; do
  sig=$(grep -E "(theorem|lemma) +([A-Za-z0-9_.]*\.)?${n}[ ({:]" "$W/condsigs.txt" | head -1)
  b=$(echo "$sig" | grep -oE '\((h[A-Za-z0-9_]*|[a-z][A-Za-z0-9_]*) *: *[A-Za-z0-9_.]*(Statement|Input|Inputs|Hypothesis)(\.\{[^}]*\})? *\)' | tr '\n' ' ')
  echo "$n: $b"
done < "$W/hits.txt"
