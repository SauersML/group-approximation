#!/usr/bin/env bash
# Generate Cairn fix nodes for the red modules of the 3c8b417428 trusted build (text generation only).
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
E=$GQ/work/bh-pal-integrate/scratch/errindex-3c8b417428.txt
W=$GQ/work/fix-graph-lead; mkdir -p $W/research
cd /Users/user/nonsofic_existence || exit 2
RED=$W/red.txt
grep -oE 'GroupApproximation/[A-Za-z0-9_/]+\.lean' $E | awk '!s[$0]++' > $RED
slug() { # path -> fix id (<=64 chars)
  s=${1#GroupApproximation/}; s=${s%.lean}
  s=$(echo "$s" | sed -e 's|^BooneHigman/Metabelian/|bhmet/|' -e 's|^Manuscript/SimpleKazhdanSofic/|sk/|')
  s=$(echo "$s" | sed -E 's/([a-z0-9])([A-Z])/\1-\2/g; s/([A-Z])([A-Z][a-z])/\1-\2/g' | tr 'A-Z/_' 'a-z--' | tr -s '-')
  echo "fix-$s" | cut -c1-64 | sed 's/-$//'
}
: > $W/nodes.tsv
while read -r f; do
  id=$(slug "$f"); mod=$(echo "${f%.lean}" | tr / .)
  echo "$id	$f	$mod" >> $W/nodes.tsv
done < $RED
while IFS=$'\t' read -r id f mod; do
  errs=$(grep -F "$f:" $E | head -4 | cut -c1-220)
  nerr=$(grep -cF "$f:" $E)
  reqs=""
  for imp in $(git show "refs/remotes/origin/main:$f" 2>/dev/null | awk '/^import GroupApproximation/{print $2}'); do
    ip="$(echo "$imp" | tr . /).lean"
    rid=$(awk -F'\t' -v p="$ip" '$2==p{print $1}' $W/nodes.tsv)
    [ -n "$rid" ] && [ "$rid" != "$id" ] && reqs="$reqs $rid"
  done
  changed=no; git diff --quiet 3c8b417428 refs/remotes/origin/main -- "$f" 2>/dev/null || changed=yes
  case "$f" in GroupApproximation/Manuscript/*) owner=ms-green-sk;; *) owner=bh-pal-wire;; esac
  short=$(echo "$errs" | head -1 | sed -E 's/^error: [^ ]+: //' | tr -d '"`')
  [ ${#short} -gt 70 ] && short="$(echo "$short" | cut -c1-70 | sed -E 's/ [^ ]*$//') ..."
  {
    echo "---"; echo "rg: 2"; echo "id: $id"; echo "kind: route"
    echo "title: \"Fix $mod: $short\""
    if [ -n "$reqs" ]; then echo "requires:"; for r in $reqs; do echo "  - $r"; done; fi
    echo "---"; echo
    echo "**OPEN.** Lean module \`$f\` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; $nerr error lines)."
    echo "It is part of the Cairn fix graph (index \`board/FIX-GRAPH.md\` in the swarm workspace). Owner: $owner."
    echo "Source changed on main since that build: $changed."
    echo; echo "**First errors (verbatim).**"; echo; echo '```'; echo "$errs"; echo '```'
    echo; echo "**What it needs.** Make \`$mod\` compile with the repository's \`-DwarningAsError=true\` settings, changing no statement."
    if [ -n "$reqs" ]; then echo "Its red imports have their own fix nodes (listed in \`requires\`). Fix those first, since errors here may be knock-on."
    else echo "No imported module is red in that build, so this is a leaf: its errors are its own."; fi
    echo; echo "**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to"
    echo "\`**RESOLVED (<green commit>).**\`."
  } > $W/research/$id.md
done < $W/nodes.tsv
wc -l < $W/nodes.tsv; awk -F'\t' '{print length($1), $1}' $W/nodes.tsv | sort -rn | head -3
grep -l '^requires:' $W/research/*.md | wc -l
