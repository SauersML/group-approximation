#!/usr/bin/env bash
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
E=$GQ/work/bh-pal-integrate/scratch/errindex-3c8b417428.txt
cd /Users/user/nonsofic_existence || exit 2
grep -oE 'GroupApproximation/BooneHigman/Metabelian/[A-Za-z0-9_/]+\.lean' $E | sort -u | while read -r p; do
  first=$(grep -m1 -F "$p" $E | sed "s|error: $p:||" | cut -c1-110)
  n=$(grep -cF "$p" $E)
  ch=$(git log --format='%h %ci' 3c8b417428..refs/remotes/origin/main -- "$p" | head -1)
  wire=$([ -f "$GQ/work/bh-pal-wire/$p" ] && echo W || echo -)
  printf '%s\t%s\t%s\t%s\t%s\n' "$p" "$n" "$wire" "${ch:-unchanged}" "$first"
done
