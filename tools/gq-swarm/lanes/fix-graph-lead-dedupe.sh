#!/usr/bin/env bash
# Merge fix-bh-a's duplicate BH fix nodes into fix-graph-lead's, and mark theirs superseded (text only).
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
W=$GQ/work/fix-graph-lead; mkdir -p $W/research
cd /Users/user/nonsofic_existence || exit 2
BASE=$(git rev-parse refs/remotes/origin/main); echo "$BASE" > $W/GQ_BASE
: > $W/dedupe-map.tsv
for f in $(git ls-tree --name-only $BASE research/ | grep '^research/fix-bh-met-'); do
  git show $BASE:$f > $W/$f
  mod=$(grep -oE 'GroupApproximation/BooneHigman/Metabelian/[A-Za-z0-9_/]+\.lean' $W/$f | head -1)
  mine=$(awk -F'\t' -v p="$mod" '$2==p{print $1}' $W/nodes.tsv)
  [ -n "$mine" ] || { echo "NO MATCH for $f ($mod)"; continue; }
  kind=$(grep -m1 '^\*\*Kind\.\*\*' $W/$f | sed 's/^\*\*Kind\.\*\* *//')
  tgt=$(awk '/^---$/{n++; next} n==1 && /^target:/{print $2}' $W/$f)
  printf '%s\t%s\t%s\t%s\n' "$f" "$mine" "$kind" "$tgt" >> $W/dedupe-map.tsv
  # theirs: status SUPERSEDED + pointer line after the frontmatter
  perl -0pi -e "s/^status: OPEN\$/status: SUPERSEDED/m; s/\A(---\n.*?\n---\n)/\$1\n**SUPERSEDED by \`$mine\`.** Duplicate fix node for the same module, landed in parallel; its classification and target are merged there. Track this module only on \`$mine\`.\n/s" $W/$f
  # mine: fresh copy from main, then add target + kind
  git show $BASE:research/$mine.md > $W/research/$mine.md
  if [ -n "$tgt" ] && ! grep -q '^target:' $W/research/$mine.md; then
    perl -0pi -e "s/^kind: route\$/kind: route\ntarget: $tgt/m" $W/research/$mine.md
  fi
  if [ -n "$kind" ] && ! grep -q '^\*\*Kind\.\*\*' $W/research/$mine.md; then
    perl -0pi -e "s/(\n\*\*What it needs\.\*\*)/\n**Kind.** $kind (classification merged from the parallel node \`${f#research/}\`, now superseded).\n\$1/" $W/research/$mine.md
    perl -0pi -e 's/\.md`, now superseded/`, now superseded/' $W/research/$mine.md
  fi
done
wc -l < $W/dedupe-map.tsv
