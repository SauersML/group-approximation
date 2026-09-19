#!/usr/bin/env bash
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
cd /Users/user/nonsofic_existence
echo "== NEWER (diff vs origin/main) =="
while read -r f; do
  rel=${f#$GQ/work/}; lane=${rel%%/*}; p=${rel#*/}
  a=$(git show "origin/main:$p" 2>/dev/null | wc -l | tr -d ' '); b=$(wc -l < "$f" | tr -d ' ')
  st=$(git diff --no-index --numstat <(git show "origin/main:$p") "$f" 2>/dev/null | awk '{print "+"$1" -"$2}')
  last=$(git log -1 --format='%h %ci %s' origin/main -- "$p" | cut -c1-90)
  echo "$lane $p main=$a disk=$b $st mtime=$(stat -f %Sm -t '%H:%M' "$f") | $last"
done < $GQ/state/unlanded-newer.txt
echo "== MISSING (frontmatter) =="
for f in $(grep '^MISSING' $GQ/state/unlanded-scan.txt | cut -d' ' -f2); do
  echo "--- ${f#$GQ/work/} lines=$(wc -l < "$f") mtime=$(stat -f %Sm -t '%H:%M' "$f")"
  awk 'NR==1{next} /^---$/{exit} {print}' "$f" | grep -E '^(id|kind|status|target|requires|title):' | cut -c1-160
  tail -2 "$f" | cut -c1-160
done
