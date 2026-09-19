#!/usr/bin/env bash
# Land lane copies that are NEWER than main's last change to the same path (lane mtime > main commit time).
# The lander's clobber guard refuses any path whose last main change was not this lane's own landing.
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
cd /Users/user/nonsofic_existence || exit 2
T=$GQ/state/unlanded2.tsv; C=$GQ/state/diff-newer.tsv; : > $C
awk -F'\t' '$1=="DIFF"' $T | while IFS=$'\t' read -r st kind lane p mt; do
  case "$p" in */.!*) continue;; esac
  lt=$(stat -f %m "$GQ/work/$lane/$p"); mct=$(git log -1 --format=%ct refs/remotes/origin/main -- "$p")
  [ "$lt" -gt "$((mct + 60))" ] && printf '%s\t%s\t%s\n' "$lane" "$kind" "$p" >> $C
done
echo "newer-than-main: $(wc -l < $C)"; cut -f1 $C | sort | uniq -c | sort -rn | head -30
for lane in $(cut -f1 $C | sort -u); do
  m=$GQ/msgs/sweepd-$lane.txt
  printf 'Land %s in-progress edits (coordinator sweep: everything on main, red allowed)\n\nLane copies newer than main. Only paths whose last change on main was this lane'"'"'s own landing pass the lander'"'"'s clobber guard.\n' "$lane" > $m
  for p in $(awk -F'\t' -v l="$lane" '$1==l{print $3}' $C); do
    o=$(timeout 600 bash $GQ/gqland-lean.sh "$lane" "$m" "$p" 2>&1)
    echo "$lane $p: $(echo "$o" | grep -oE 'LANDED [0-9a-f]+|REFUSED[^.]*' | head -1 | cut -c1-110)"
  done
done
