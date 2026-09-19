#!/usr/bin/env bash
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
W=$GQ/work/bh-free-54; cd /Users/user/nonsofic_existence
find $W/research -type f -name '*.md' | while read -r f; do p=${f#$W/}
  if ! git cat-file -e "origin/main:$p" 2>/dev/null; then echo "MISSING $p $(stat -f %Sm -t %H:%M "$f")"; continue; fi
  if [ "$(git rev-parse origin/main:$p)" = "$(git hash-object "$f")" ]; then echo "SAME $p"; else echo "DIFF $p disk=$(wc -l <"$f"|tr -d ' ') main=$(git show origin/main:$p|wc -l|tr -d ' ') mtime=$(stat -f %Sm -t %H:%M "$f") mainlast=$(git log -1 --format=%ci origin/main -- $p|cut -c12-16)"; fi
done
