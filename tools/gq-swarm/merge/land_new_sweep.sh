#!/usr/bin/env bash
# Land every NEW (absent from origin/main) lane file under its own lane name. Red Lean is fine (user order 09-18).
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
cd /Users/user/nonsofic_existence || exit 2
T=$GQ/state/unlanded2.tsv
for lane in $(awk -F'\t' '$1=="NEW"{print $3}' $T | sort -u); do
  [ "$lane" = team-lead ] && continue
  paths=$(awk -F'\t' -v l="$lane" '$1=="NEW" && $3==l {print $4}' $T | while read -r p; do git cat-file -e "refs/remotes/origin/main:$p" 2>/dev/null || echo "$p"; done)
  [ -z "$paths" ] && continue
  m=$GQ/msgs/sweep-$lane.txt
  printf 'Land %s work in progress (coordinator sweep: everything on main, red allowed)\n\nFiles the lane had drafted but not yet landed. Lean modules are unwired (not imported by the root) and may not build yet; fixes are tracked in the Cairn fix graph (research/fix-*.md).\n' "$lane" > $m
  echo "### $lane: $(echo $paths | wc -w | tr -d ' ') files"
  # shellcheck disable=SC2086
  out=$(timeout 900 bash $GQ/gqland-lean.sh "$lane" "$m" $paths 2>&1); echo "$out" | grep -E 'LANDED|REFUSED|ABORT|GAVE UP' | head -3
  if echo "$out" | grep -q REFUSED; then
    for p in $paths; do
      o=$(timeout 600 bash $GQ/gqland-lean.sh "$lane" "$m" "$p" 2>&1); echo "   $p: $(echo "$o" | grep -oE 'LANDED [0-9a-f]+|REFUSED.*' | head -1 | cut -c1-150)"
    done
  fi
done
