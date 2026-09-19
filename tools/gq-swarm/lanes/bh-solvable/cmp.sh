#!/usr/bin/env bash
W=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq/work/bh-solvable
cd /Users/user/nonsofic_existence
for f in $(cd $W && find research -type f -name '*.md'); do
  if ! git cat-file -e "origin/main:$f" 2>/dev/null; then echo "MISSING $f"; continue; fi
  if [ "$(git rev-parse origin/main:$f)" = "$(git hash-object $W/$f)" ]; then echo "SAME $f"; else
    echo "DIFF $f main=$(git show origin/main:$f | wc -l | tr -d ' ') disk=$(wc -l < $W/$f | tr -d ' ') last=$(git log -1 --format='%h %ci %an %s' origin/main -- $f | cut -c1-100)"; fi
done
