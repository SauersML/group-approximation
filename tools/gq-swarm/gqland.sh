#!/usr/bin/env bash
# gqland.sh <lane> <msgfile> <path> [<path> ...]
#
# GL_n(Q) swarm lander.  Lands research files drafted under $GQ/work/<lane>/<path> onto origin/main as ONE
# commit built from the CURRENT origin/main tree with a PRIVATE index.  It never touches the shared checkout,
# its index, HEAD, branches or worktrees.
#
# Allowed paths:  research/<id>.md  (id ^[a-z0-9][a-z0-9-]{1,63}$, never FRONTIER.md)
#                 research/artifacts/gq-<anything>.md
# Guards: serialized by flock; disk >= 2 GiB free; forbidden tokens; frontmatter lint (id == file stem, kind,
# requires/target/artifacts exist on origin/main or in this call); clobber guard for files already on main;
# read-tree exit + entry-count guard; the commit may add/modify exactly the given paths and delete nothing.
# Env: GQ_BASE=<origin sha>  the sha your copy of an EXISTING file was taken from (required to edit one).
set -uo pipefail
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
REPO=/Users/user/nonsofic_existence
LANE=${1:?usage: gqland.sh <lane> <msgfile> <path...>}; MSG=${2:?msgfile}; shift 2
[ $# -ge 1 ] || { echo "usage: gqland.sh <lane> <msgfile> <path...>"; exit 2; }
[ -s "$MSG" ] || { echo "REFUSED: empty message file $MSG"; exit 2; }
SRC="$GQ/work/$LANE"
mkdir -p "$GQ/state" "$GQ/msgs"
cd "$REPO" || exit 2

AVAIL_KB=$(df -k /System/Volumes/Data | awk 'NR==2{print $4}')
[ "${AVAIL_KB:-0}" -ge 2097152 ] || { echo "REFUSED: under 2 GiB free on disk; tell team-lead"; exit 2; }

if grep -qiE 'wafer|waffle|claude-(opus|sonnet|haiku|fable)|\bfable\b|sauerslabs|Claude-Session' "$MSG"; then
  echo "REFUSED: forbidden token in commit message"; exit 2; fi

for p in "$@"; do
  case "$p" in
    research/FRONTIER.md) echo "REFUSED: FRONTIER.md is generated"; exit 2;;
    research/artifacts/gq-*.md) ;;
    research/*/*) echo "REFUSED: $p (only research/<id>.md and research/artifacts/gq-*.md)"; exit 2;;
    research/*.md)
      stem=$(basename "$p" .md)
      echo "$stem" | grep -qE '^[a-z0-9][a-z0-9-]{1,63}$' || { echo "REFUSED: bad id '$stem' (^[a-z0-9][a-z0-9-]{1,63}\$)"; exit 2; };;
    *) echo "REFUSED: $p (only research/<id>.md and research/artifacts/gq-*.md)"; exit 2;;
  esac
  [ -f "$SRC/$p" ] || { echo "REFUSED: missing $SRC/$p"; exit 2; }
  if grep -qiE 'wafer|waffle|claude-(opus|sonnet|haiku|fable)|\bfable\b|sauerslabs|Claude-Session' "$SRC/$p"; then
    echo "REFUSED: forbidden token (model name/id or email) in $p"; exit 2; fi
done

exists_or_in_call() {  # $1 = repo path
  local q; for q in "${ALL[@]}"; do [ "$q" = "$1" ] && return 0; done
  git cat-file -e "refs/remotes/origin/main:$1" 2>/dev/null
}
ALL=("$@")

exec 9>"$GQ/state/land.lock"
flock -w 900 9 || { echo "GAVE UP: land lock busy for 15 min"; exit 1; }
for f in 1 2 3 4 5; do git fetch -q origin main 2>/dev/null && break; sleep 2; done

# Frontmatter lint for node files.
for p in "$@"; do
  case "$p" in research/artifacts/*) continue;; esac
  F="$SRC/$p"; stem=$(basename "$p" .md)
  [ "$(head -1 "$F")" = "---" ] || { echo "REFUSED: $p must start with a --- frontmatter line"; exit 2; }
  FM=$(awk 'NR==1{next} /^---$/{exit} {print}' "$F")
  echo "$FM" | grep -qxF "id: $stem" || { echo "REFUSED: $p needs 'id: $stem' in its frontmatter"; exit 2; }
  echo "$FM" | grep -qE '^kind: (claim|route)$' || { echo "REFUSED: $p needs 'kind: claim' or 'kind: route'"; exit 2; }
  echo "$FM" | grep -qxF 'rg: 2' || { echo "REFUSED: $p needs 'rg: 2'"; exit 2; }
  echo "$FM" | grep -qE '^title: .+' || { echo "REFUSED: $p needs a 'title: <one line>' in its frontmatter (routes too)"; exit 2; }
  T=$(echo "$FM" | sed -n 's/^target:[[:space:]]*//p')
  if [ -n "$T" ]; then exists_or_in_call "research/$T.md" || { echo "REFUSED: $p target '$T' is not on origin/main or in this call"; exit 2; }; fi
  for key in requires invalidates; do
    for r in $(echo "$FM" | awk -v k="$key:" '$1==k{on=1; if (NF>1 && $2!="[]") {gsub(/[\[\],]/," "); for(i=2;i<=NF;i++) print $i}; next} on && /^[[:space:]]+-[[:space:]]/{print $2; next} on && /^[^[:space:]]/{on=0}'); do
      exists_or_in_call "research/$r.md" || { echo "REFUSED: $p $key '$r' is not on origin/main or in this call"; exit 2; }
    done
  done
  for a in $(echo "$FM" | awk '$1=="artifacts:"{on=1; next} on && /^[[:space:]]+-[[:space:]]/{print $2; next} on && /^[^[:space:]]/{on=0}'); do
    exists_or_in_call "$a" || { echo "REFUSED: $p artifact '$a' is not on origin/main or in this call"; exit 2; }
  done
done

# Refresh origin/main before the clobber guard so it never compares against a stale ref (09-18: a stale-base landing overwrote a peer edit).
for f in 1 2 3; do timeout 60 git fetch -q origin main 2>/dev/null && break; sleep 2; done
# Clobber guard for files that already exist on origin/main.
for p in "$@"; do
  git cat-file -e "refs/remotes/origin/main:$p" 2>/dev/null || continue
  [ "$(git rev-parse "refs/remotes/origin/main:$p")" = "$(git hash-object "$SRC/$p")" ] && continue
  lastc=$(git log -1 --format=%H refs/remotes/origin/main -- "$p")
  grep -qE " $LANE $lastc( |\$)" "$GQ/state/landed.log" 2>/dev/null && continue
  # GQ_BASE exempts ONLY the existing files you deliberately copied and edited, named in GQ_BASE_PATHS
  # (space-separated). A file you believe is new but which already exists on origin/main is refused.
  if [ -n "${GQ_BASE:-}" ]; then
    [ -n "${GQ_BASE_PATHS:-}" ] || { echo "REFUSED: GQ_BASE is set but GQ_BASE_PATHS is not; list the existing files you copied and edited, e.g. GQ_BASE_PATHS=\"$p\""; exit 2; }
    case " $GQ_BASE_PATHS " in *" $p "*)
      if git merge-base --is-ancestor "$lastc" "$GQ_BASE" 2>/dev/null; then continue; fi;;
    esac
  fi
  echo "REFUSED (clobber guard): $p on origin/main was last changed by $(git log -1 --format='%h %an: %s' "$lastc"), which is not your landing and not in GQ_BASE. Re-copy it (git show origin/main:$p), redo your edit, and land with GQ_BASE=<that origin sha>."
  exit 2
done

MSGF=$(mktemp "$GQ/msgs/land.XXXXXX"); cat "$MSG" > "$MSGF"
grep -q '^Co-Authored-By:' "$MSGF" || printf '\nCo-Authored-By: Claude Code <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01Cx1kxpcwHuuQ8mqh4hcKQy\n' >> "$MSGF"
CACHEINFO=()
for p in "$@"; do BLOB=$(git hash-object -w "$SRC/$p") || exit 1; CACHEINFO+=("100644,$BLOB,$p"); done
WANT=$(printf '%s\n' "$@" | sort -u)
# Blob of each path on origin/main when the clobber guard passed (NONE = absent). Every retry re-checks it, so a
# rebuild on a newer origin/main can never overwrite a concurrent edit of the same file.
ORIGB=(); for p in "$@"; do ORIGB+=("$(git rev-parse -q --verify "refs/remotes/origin/main:$p" 2>/dev/null || echo NONE)"); done
for attempt in $(seq 1 30); do
  [ "$attempt" -gt 1 ] && for f in 1 2 3 4 5; do git fetch -q origin main 2>/dev/null && break; sleep 2; done
  BASE=$(git rev-parse refs/remotes/origin/main)
  i=0
  for p in "$@"; do
    cur=$(git rev-parse -q --verify "$BASE:$p" 2>/dev/null || echo NONE)
    [ "$cur" = "${ORIGB[$i]}" ] || { echo "REFUSED: $p changed on origin/main while this landing was retrying (last: $(git log -1 --format='%h %an: %s' "$BASE" -- "$p")). Re-copy it with git show origin/main:$p, redo your edit, and land with GQ_BASE=<that sha>."; exit 2; }
    i=$((i+1))
  done
  BASEN=$(git ls-tree -r --name-only "$BASE" | wc -l | tr -d ' ')
  [ "$BASEN" -gt 1000 ] || { echo "REFUSED: origin/main tree listing looks wrong ($BASEN entries)"; exit 1; }
  IDX=$(mktemp "$GQ/msgs/idx.XXXXXX"); rm -f "$IDX"; export GIT_INDEX_FILE="$IDX"
  if ! git read-tree "$BASE"; then unset GIT_INDEX_FILE; rm -f "$IDX"; echo "ABORT: read-tree failed"; exit 1; fi
  IDXN=$(git ls-files | wc -l | tr -d ' ')
  [ "$IDXN" = "$BASEN" ] || { unset GIT_INDEX_FILE; rm -f "$IDX"; echo "ABORT: private index has $IDXN entries, base tree has $BASEN"; exit 1; }
  for ci in "${CACHEINFO[@]}"; do git update-index --add --cacheinfo "$ci" || { unset GIT_INDEX_FILE; rm -f "$IDX"; exit 1; }; done
  TREE=$(git write-tree) || { unset GIT_INDEX_FILE; rm -f "$IDX"; exit 1; }
  unset GIT_INDEX_FILE; rm -f "$IDX"
  if [ "$TREE" = "$(git rev-parse "${BASE}^{tree}")" ]; then echo "NOTHING TO LAND: identical to origin/main $(git rev-parse --short "$BASE")"; rm -f "$MSGF"; exit 0; fi
  NEWN=$(git ls-tree -r --name-only "$TREE" | wc -l | tr -d ' ')
  [ "$NEWN" -ge "$BASEN" ] || { echo "ABORT: new tree has fewer entries ($NEWN < $BASEN)"; exit 1; }
  NEW=$(git commit-tree "$TREE" -p "$BASE" -F "$MSGF") || exit 1
  BADST=$(git diff --name-status "$BASE" "$NEW" | awk '$1!="A" && $1!="M"')
  [ -z "$BADST" ] || { echo "REFUSED: commit would delete or rename:"; echo "$BADST"; exit 2; }
  EXTRA=$(comm -23 <(git diff --name-only "$BASE" "$NEW" | sort) <(echo "$WANT"))
  [ -z "$EXTRA" ] || { echo "REFUSED: commit would touch unexpected paths:"; echo "$EXTRA"; exit 2; }
  ERRF=$(mktemp "$GQ/msgs/push.XXXXXX")
  if git -c credential.helper= -c credential.helper='!f() { echo "username=SauersML"; echo "password=$(gh auth token -u SauersML)"; }; f' \
       push -q origin "$NEW:refs/heads/main" 2>"$ERRF"; then
    git update-ref refs/remotes/origin/main "$NEW" 2>/dev/null
    echo "LANDED $(git rev-parse --short "$NEW") on origin/main (parent $(git rev-parse --short "$BASE")):"
    git show --stat --format= "$NEW" | tail -n +1
    echo "$(date '+%F %T') $LANE $NEW $*" >> "$GQ/state/landed.log"
    rm -f "$ERRF" "$MSGF"; exit 0
  fi
  sleep $(( (RANDOM % 4) + 1 ))
done
echo "GAVE UP after 30 push attempts; last error:"; cat "$ERRF" 2>/dev/null; exit 1
