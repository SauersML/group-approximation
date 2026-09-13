#!/bin/bash
S=/private/tmp/claude-501/-Users-user-nonsofic-existence/0a930a1d-0cf3-4aa0-b91a-b8bfce7d68c7/scratchpad/gk/state
L=/private/tmp/claude-501/-Users-user-nonsofic-existence/0a930a1d-0cf3-4aa0-b91a-b8bfce7d68c7/scratchpad/gk/lanes/w3-strategist-gate
SEEN="$L/monitor-seen.txt"; touch "$SEEN"; shopt -s nullglob
until [ -f "$L/STOP" ]; do
  for f in "$S"/pushed-w4-r4-*.tsv "$S"/pushed-w4-heisenberg.tsv "$S"/pushed-w4-gate-descent.tsv "$S"/pushed-w4-vf-gate.tsv \
           "$S"/pushed-w4-sub-*.tsv "$S"/pushed-w5-sub-*.tsv "$S"/pushed-w5-commutant-distort.tsv "$S"/pushed-w6-mismatch-*.tsv \
           "$S"/pushed-w5-c3-descent.tsv "$S"/pushed-w5-c3-submult.tsv "$S"/pushed-w5-cohn-lef.tsv "$S"/pushed-w5-v-*.tsv "$S"/pushed-w6-v-extend.tsv; do
    [ -f "$f" ] || continue; lane=$(basename "$f" .tsv); lane=${lane#pushed-}
    while IFS=$'\t' read -r p sha rest; do [ -n "$p" ] || continue
      key="$lane	$p	$sha"
      if ! grep -qxF "$key" "$SEEN"; then printf '%s\n' "$key" >> "$SEEN"; printf 'LANDED %s %s %s\n' "$lane" "$p" "${sha:0:10}"; fi
    done < "$f"
  done
  sleep 20
done
echo "MONITOR STOP sentinel seen"
