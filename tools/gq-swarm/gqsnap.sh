#!/bin/bash
# gqsnap.sh: snapshot swarm coordination files (lander, RULES, ROSTER, boards, landed.log) to origin/main under tools/gq-swarm/.
# Additions/modifications only, private index, guarded like gqland.sh. Usage: gqsnap.sh
set -u
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
cd /Users/user/nonsofic_existence || exit 1
exec 9>"$GQ/state/land.lock"; flock -w 600 9 || { echo "lock timeout"; exit 1; }
FREE=$(df -k / | awk 'NR==2{print $4}'); [ "$FREE" -gt 2097152 ] || { echo "REFUSED: under 2 GiB free"; exit 2; }
for f in 1 2 3; do timeout 60 git fetch -q origin main 2>/dev/null && break; sleep 2; done
declare -a SRCS=("$GQ/gqland.sh:tools/gq-swarm/gqland.sh" "$GQ/gqsnap.sh:tools/gq-swarm/gqsnap.sh" "$GQ/RULES.md:tools/gq-swarm/RULES.md" "$GQ/ROSTER.md:tools/gq-swarm/ROSTER.md" "$GQ/state/landed.log:tools/gq-swarm/state/landed.log")
for b in $GQ/board/*.md; do SRCS+=("$b:tools/gq-swarm/board/$(basename $b)"); done
for attempt in 1 2 3 4 5 6; do
  [ "$attempt" -gt 1 ] && { sleep 3; timeout 60 git fetch -q origin main 2>/dev/null; }
  BASE=$(git rev-parse refs/remotes/origin/main); BASEN=$(git ls-tree -r --name-only "$BASE" | wc -l | tr -d ' ')
  [ "$BASEN" -gt 1000 ] || { echo "ABORT: base listing $BASEN"; exit 1; }
  IDX=$(mktemp "$GQ/msgs/sidx.XXXXXX"); rm -f "$IDX"; export GIT_INDEX_FILE="$IDX"
  git read-tree "$BASE" || { unset GIT_INDEX_FILE; rm -f "$IDX"; echo "ABORT read-tree"; exit 1; }
  [ "$(git ls-files | wc -l | tr -d ' ')" = "$BASEN" ] || { unset GIT_INDEX_FILE; rm -f "$IDX"; echo "ABORT index count"; exit 1; }
  WANT=""
  for s in "${SRCS[@]}"; do src=${s%%:*}; dst=${s#*:}; BLOB=$(git hash-object -w "$src") || exit 1; git update-index --add --cacheinfo "100644,$BLOB,$dst" || exit 1; WANT="$WANT$dst"$'\n'; done
  TREE=$(git write-tree) || exit 1; unset GIT_INDEX_FILE; rm -f "$IDX"
  [ "$TREE" = "$(git rev-parse "${BASE}^{tree}")" ] && { echo "NOTHING TO SNAPSHOT"; exit 0; }
  NEWN=$(git ls-tree -r --name-only "$TREE" | wc -l | tr -d ' '); [ "$NEWN" -ge "$BASEN" ] || { echo "ABORT fewer entries"; exit 1; }
  MSGF=$(mktemp "$GQ/msgs/smsg.XXXXXX"); printf 'Snapshot the GL_n(Q) and Boone-Higman swarm coordination files under tools/gq-swarm\n\nLander, lane rules, roster, lane boards and the landing log, so the swarm state survives a reboot of the scratchpad.\n\nCo-Authored-By: Claude Code <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01Cx1kxpcwHuuQ8mqh4hcKQy\n' > "$MSGF"
  NEW=$(git commit-tree "$TREE" -p "$BASE" -F "$MSGF") || exit 1
  BAD=$(git diff --name-status "$BASE" "$NEW" | awk '$1!="A" && $1!="M"'); [ -z "$BAD" ] || { echo "REFUSED del/rename: $BAD"; exit 2; }
  EXTRA=$(comm -23 <(git diff --name-only "$BASE" "$NEW" | sort) <(printf '%s' "$WANT" | sort -u)); [ -z "$EXTRA" ] || { echo "REFUSED extra: $EXTRA"; exit 2; }
  if git -c credential.helper= -c credential.helper='!f() { echo "username=SauersML"; echo "password=$(gh auth token -u SauersML)"; }; f' push -q origin "$NEW:refs/heads/main" 2>/dev/null; then
    git update-ref refs/remotes/origin/main "$NEW"; echo "SNAPSHOT LANDED $(git rev-parse --short $NEW) ($(git diff --name-only $BASE $NEW | wc -l | tr -d ' ') files)"; exit 0
  fi
done
echo "push failed after retries"; exit 1
