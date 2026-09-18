#!/bin/bash
# After the merge lands: delete merged GitHub branches (with a lease on the tip that was checked), archive the one
# already-deleted branch whose tip main lacks, and drop stale local refs and dead worktree metadata.
# DO=1 acts; otherwise it only reports.
set -uo pipefail
REPO=/Users/user/nonsofic_existence
S=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/merge
DO=${DO:-0}
cd "$REPO" || exit 1
run() { if [ "$DO" = 1 ]; then "$@"; else echo "WOULD: $*"; fi; }
git fetch -q origin +refs/heads/main:refs/remotes/origin/main || { echo "ABORT: fetch"; exit 1; }
MAIN=$(git rev-parse refs/remotes/origin/main)
echo "origin main $MAIN"

# 1. Merged branches on GitHub: delete only when the tip origin holds right now is contained in main.
for b in claude/affectionate-albattani-ckvc5v claude/agent-limit-config-yhbm8h claude/scale-agents-high-impact-erol9w; do
  sha=$(git ls-remote origin "refs/heads/$b" | cut -f1)
  if [ -z "$sha" ]; then echo "GONE $b"; continue; fi
  git cat-file -e "${sha}^{commit}" 2>/dev/null || git fetch -q origin "+refs/heads/$b:refs/remotes/origin/$b"
  if ! git merge-base --is-ancestor "$sha" "$MAIN"; then echo "SKIP $b: tip $sha is not in main"; continue; fi
  if [ "$DO" = 1 ]; then
    if git push --force-with-lease="refs/heads/$b:$sha" origin ":refs/heads/$b" > "$S/del.log" 2>&1; then
      if [ -z "$(git ls-remote origin "refs/heads/$b")" ]; then echo "DELETED $b (tip $sha in main)"; else echo "DELETE REPORTED OK BUT $b IS STILL ON ORIGIN"; fi
    else cat "$S/del.log"; echo "FAILED to delete $b"; fi
  else echo "WOULD DELETE origin $b ($sha, in main)"; fi
done

# 2. pestov91-three-coordinate-publication-20260913 is already gone from GitHub and its tip is not in main
#    (22 of its 23 files are on main byte for byte; its PDF is an older main blob).  Pin the tip under refs/archive.
PT=$(git rev-parse -q --verify refs/remotes/origin/pestov91-three-coordinate-publication-20260913)
if [ -n "$PT" ]; then
  have=$(git ls-remote origin refs/archive/pestov91-three-coordinate-publication-20260913 | cut -f1)
  if [ "$have" = "$PT" ]; then echo "archive ref already holds $PT"
  elif [ -z "$have" ]; then run git push origin "$PT:refs/archive/pestov91-three-coordinate-publication-20260913"
  else echo "SKIP archive: refs/archive/pestov91... holds $have, not $PT"; fi
fi

# 3. Stale local tracking refs.
PS=$(git rev-parse -q --verify refs/remotes/origin/palomar-stw-xxii-submit-20260913)
if [ -n "$PS" ] && [ "$(git ls-remote origin refs/archive/palomar-stw-xxii-submit-20260913 | cut -f1)" = "$PS" ]; then
  run git update-ref -d refs/remotes/origin/palomar-stw-xxii-submit-20260913 "$PS"
fi
if [ -n "$PT" ]; then
  if [ "$DO" != 1 ] || [ "$(git ls-remote origin refs/archive/pestov91-three-coordinate-publication-20260913 | cut -f1)" = "$PT" ]; then
    run git update-ref -d refs/remotes/origin/pestov91-three-coordinate-publication-20260913 "$PT"
  else echo "KEEP local pestov91 tracking ref: archive ref not confirmed"; fi
fi
KT=$(git rev-parse -q --verify refs/remotes/kt-fixedpoint/main)
if [ -n "$KT" ] && git merge-base --is-ancestor "$KT" "$MAIN"; then run git update-ref -d refs/remotes/kt-fixedpoint/main "$KT"; fi
# No `git remote prune`: it would drop the pestov91 tracking ref even when the archive push failed.  Both stale
# tracking refs are handled explicitly above.

# 4. Worktree metadata whose directories no longer exist.
if [ "$DO" = 1 ]; then git worktree prune -v; else git worktree prune --dry-run -v | wc -l | xargs echo "WOULD prune worktree entries:"; fi

echo "=== origin heads now ==="; git ls-remote --heads origin
echo "=== local refs now ==="; git for-each-ref --format='%(refname)' refs/heads refs/remotes
