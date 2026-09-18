#!/usr/bin/env bash
set -uo pipefail
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
cd /Users/user/nonsofic_existence || exit 2
D=experiments/hnn-rewriting-2026-09-17/out
FILES=("$D/basilicaHNN-AatT-wreath.txt" "$D/basilicaHNN-AatT-wreath.txt.log" "$D/bs12-TtAa-wreath.txt.log")
exec 9>"$GQ/state/land.lock"; flock -w 900 9 || { echo "lock busy"; exit 1; }
for a in 1 2 3; do
  timeout 60 git fetch -q origin main || { sleep 3; continue; }
  BASE=$(git rev-parse refs/remotes/origin/main)
  # never overwrite a concurrent edit: each file on origin must still equal the checkout's HEAD copy
  for f in "${FILES[@]}"; do [ "$(git rev-parse "$BASE:$f")" = "$(git rev-parse "HEAD:$f")" ] || { echo "REFUSED: $f changed on origin"; exit 2; }; done
  BASEN=$(git ls-tree -r --name-only "$BASE" | wc -l | tr -d ' '); [ "$BASEN" -gt 1000 ] || exit 1
  IDX=$(mktemp "$GQ/msgs/idx.XXXXXX"); rm -f "$IDX"; export GIT_INDEX_FILE=$IDX
  git read-tree "$BASE" || { unset GIT_INDEX_FILE; rm -f "$IDX"; echo "read-tree failed"; exit 1; }
  [ "$(git ls-files | wc -l | tr -d ' ')" = "$BASEN" ] || { unset GIT_INDEX_FILE; rm -f "$IDX"; echo "index count mismatch"; exit 1; }
  for f in "${FILES[@]}"; do b=$(git hash-object -w "$f") && git update-index --cacheinfo "100644,$b,$f" || exit 1; done
  T=$(git write-tree); unset GIT_INDEX_FILE; rm -f "$IDX"
  [ "$(git diff --name-only "$BASE" "$T" | wc -l | tr -d ' ')" = 3 ] || { echo "unexpected tree diff"; exit 1; }
  C=$(printf 'Record the rerun of the bounded completion search for the Basilica HNN and BS(1,2) wreath presentations\n\nThe 09-17 23:04 rerun left these outputs uncommitted in the shared checkout. Same bounds, different\nnondeterministic trace; neither run completes.\n\nCo-Authored-By: Claude Code <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01Cx1kxpcwHuuQ8mqh4hcKQy\n' | git commit-tree "$T" -p "$BASE") || exit 1
  if timeout 120 git push -q origin "$C:refs/heads/main"; then echo "PUSHED $C"; exit 0; fi
  sleep 5
done
echo "push failed"; exit 1
