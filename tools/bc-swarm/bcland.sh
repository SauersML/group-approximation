#!/usr/bin/env bash
# BC_LANE=<lane> bcland.sh <msgfile> <repo-path>@<source-file> ... [<repo-path>@DELETE ...]
# Land additions, modifications and explicit deletions of the named paths on origin/main through a PRIVATE per-run
# index, never HEAD, the shared index or the working tree. Every per-run file (index, path lists, diff, push log) lives
# in a fresh mktemp directory under $BC/state that is removed on exit, so concurrent runs share nothing except the
# append-only per-lane push records $BC/state/pushed-<lane>.txt.
# The base and the post-push tip are resolved with `git ls-remote` and their objects fetched by SHA with
# --no-write-fetch-head, with retries: no local ref or FETCH_HEAD is written, so concurrent fetches by other lanes in
# the shared checkout cannot make a landing fail or move its base.
# Guards (09-12 wipe, 09-12 dangling import):
#  - rev-parse, read-tree, hash-object, update-index, write-tree and commit-tree must each exit 0;
#  - the base tree must carry GroupApproximation.lean and lake-manifest.json;
#  - after read-tree the private index entry count must equal the base tree entry count;
#  - the new tree's entry count must equal the base count plus new paths minus deleted paths;
#  - `git diff --no-renames --name-status BASE NEW` may name only the given paths: A or M for sources, D for deletions;
#  - a path that exists on main with different content, or that is being deleted, is refused unless a bcland push by
#    the SAME lane wrote it last;
#  - bcimportguard.sh on the commit being pushed: no deleted Lean module may still be imported by the new tree;
#  - the push names refs/heads/main explicitly; afterwards the pushed commit must be an ancestor of the remote tip, and
#    each landed blob is compared at that tip (a later commit changing a path is reported, not treated as failure).
# BC_DRYRUN=1 runs every guard and prints the candidate commit, but does not push.
set -uo pipefail
REPO=/Users/user/nonsofic_existence
BC=__SCRATCHPAD__/bc
GUARD=$BC/bcimportguard.sh
STATE=$BC/state; mkdir -p "$STATE"
TAB=$'\t'
fail() { echo "LAND REFUSED: $1"; exit 1; }
gitnoise() { grep -vE 'gc\.log|git prune|Automatic cleanup|^warning: The last gc|^$' | tail -3 | tr '\n' ' '; }
resolve_tip() {
  TIPSHA=""; local out err="" a
  for a in 1 2 3 4 5; do
    out=$(git ls-remote origin refs/heads/main 2>&1)
    TIPSHA=$(printf '%s\n' "$out" | awk '$2 == "refs/heads/main" { print $1 }')
    [[ "$TIPSHA" =~ ^[0-9a-f]{40}$ ]] && break
    TIPSHA=""; err=$(printf '%s\n' "$out" | gitnoise); sleep $((a * 2))
  done
  [ -n "$TIPSHA" ] || fail "cannot resolve the origin main tip with ls-remote after 5 attempts: $err"
  for a in 1 2 3 4 5; do
    git cat-file -e "$TIPSHA^{commit}" 2>/dev/null && return 0
    err=$(git fetch -q --no-write-fetch-head origin "$TIPSHA" 2>&1 | gitnoise)
    git cat-file -e "$TIPSHA^{commit}" 2>/dev/null && return 0
    sleep $((a * 2))
  done
  fail "cannot fetch the objects of ${TIPSHA:0:9} after 5 attempts: $err"
}
LANE=${BC_LANE:-}
[[ "$LANE" =~ ^[a-z0-9][a-z0-9-]*$ ]] || fail "set BC_LANE=<your lane name>; own-push records are kept per lane"
[ -f "$GUARD" ] || fail "import guard $GUARD is missing"
PUSHED=$STATE/pushed-$LANE.txt
touch "$PUSHED" || fail "cannot create $PUSHED"
MSG=${1:-}; [ -n "$MSG" ] || fail "usage: BC_LANE=<lane> bcland.sh <msgfile> <path@source | path@DELETE>..."
shift
[ -s "$MSG" ] || fail "empty message file $MSG"
[ $# -ge 1 ] || fail "no paths"
RUN=$(mktemp -d "$STATE/land-$LANE.XXXXXX") || fail "mktemp"
trap 'rm -rf "$RUN"' EXIT
cd "$REPO" || fail "no repo"
export GIT_INDEX_FILE=$RUN/index
CRED='!f() { echo username=SauersML; echo password=$(gh auth token -u SauersML); }; f'
own_last() {  # the path was last written, on this base, by a bcland push of this lane
  local last; last=$(git log -1 --format=%H "$BASE" -- "$1")
  grep -qxF "$last" "$PUSHED" || fail "$1 $2 on main and was last written by ${last:0:9}, not by a bcland push of lane $LANE"
}
for try in 1 2 3 4 5 6 7 8; do
  resolve_tip; BASE=$TIPSHA
  for root in GroupApproximation.lean lake-manifest.json; do
    git cat-file -e "${BASE}:${root}" 2>/dev/null || fail "origin/main@${BASE:0:9} lacks $root (gutted tree)"
  done
  N_TREE=$(git ls-tree -r --name-only "$BASE" | wc -l | tr -d ' ')
  rm -f "$GIT_INDEX_FILE"
  git read-tree "$BASE" || fail "read-tree of ${BASE:0:9} exited nonzero"
  N_IDX=$(git ls-files | wc -l | tr -d ' ')
  [ "$N_IDX" = "$N_TREE" ] || fail "private index has $N_IDX entries, base tree has $N_TREE"
  NNEW=0; NDEL=0; : > "$RUN/add"; : > "$RUN/del"; : > "$RUN/blobs"
  for spec in "$@"; do
    path=${spec%%@*}; src=${spec#*@}
    { [ -n "$path" ] && [ "$path" != "$spec" ]; } || fail "bad spec '$spec'"
    if [ "$src" = DELETE ]; then
      git rev-parse --verify -q "${BASE}:${path}" >/dev/null || fail "cannot delete $path: absent at ${BASE:0:9}"
      own_last "$path" "is being deleted"
      git update-index --force-remove -- "$path" || fail "update-index --force-remove $path"
      NDEL=$((NDEL+1)); echo "$path" >> "$RUN/del"
      continue
    fi
    [ -f "$src" ] || fail "bad spec '$spec': no source file"
    mode=100644; case "$path" in *.sh) mode=100755;; esac
    blob=$(git hash-object -w -- "$src") || fail "hash-object $src"
    if old=$(git rev-parse --verify -q "${BASE}:${path}"); then
      [ "$old" = "$blob" ] || own_last "$path" "differs"
    else
      NNEW=$((NNEW+1))
    fi
    git update-index --add --cacheinfo "$mode,$blob,$path" || fail "update-index $path"
    echo "$path" >> "$RUN/add"; echo "$blob $path" >> "$RUN/blobs"
  done
  [ -z "$(LC_ALL=C sort "$RUN/add" "$RUN/del" | uniq -d)" ] || fail "a path is both landed and deleted"
  TREE=$(git write-tree) || fail "write-tree"
  N_NEWTREE=$(git ls-tree -r --name-only "$TREE" | wc -l | tr -d ' ')
  [ "$N_NEWTREE" = "$((N_TREE + NNEW - NDEL))" ] || fail "new tree has $N_NEWTREE entries, expected $((N_TREE + NNEW - NDEL))"
  NEW=$(git commit-tree "$TREE" -p "$BASE" -F "$MSG") || fail "commit-tree"
  [ -n "$NEW" ] || fail "empty commit id"
  git diff --no-renames --name-status "$BASE" "$NEW" > "$RUN/diff" || fail "diff"
  if grep -vE "^[AMD]${TAB}" "$RUN/diff" | grep -q .; then
    fail "commit would retype: $(grep -vE "^[AMD]${TAB}" "$RUN/diff" | head -3 | tr '\n' ' ')"
  fi
  sed -n "s/^[AM]${TAB}//p" "$RUN/diff" | LC_ALL=C sort > "$RUN/changed"
  sed -n "s/^D${TAB}//p" "$RUN/diff" | LC_ALL=C sort > "$RUN/deleted"
  [ -z "$(LC_ALL=C comm -23 "$RUN/changed" <(LC_ALL=C sort -u "$RUN/add"))" ] || fail "commit adds or modifies paths outside the given sources"
  [ -z "$(LC_ALL=C comm -23 "$RUN/deleted" <(LC_ALL=C sort -u "$RUN/del"))" ] || fail "commit deletes paths outside the given deletions"
  if [ ! -s "$RUN/changed" ] && [ ! -s "$RUN/deleted" ]; then echo "LAND NOOP: every path already on main at ${BASE:0:9}"; exit 0; fi
  GOUT=$(bash "$GUARD" "$BASE" "$NEW" 2>&1); GRC=$?
  printf '%s\n' "$GOUT"
  [ $GRC -eq 0 ] || fail "import guard refused or could not read (rc=$GRC)"
  echo "candidate ${NEW:0:9} on ${BASE:0:9} (lane $LANE):"; cat "$RUN/diff"
  if [ -n "${BC_DRYRUN:-}" ]; then echo "LAND DRYRUN: every guard passed; not pushed"; exit 0; fi
  if git -c credential.helper= -c credential.helper="$CRED" push origin "${NEW}:refs/heads/main" > "$RUN/push.log" 2>&1; then
    echo "$NEW" >> "$PUSHED"
    resolve_tip; TIP=$TIPSHA
    git merge-base --is-ancestor "$NEW" "$TIP" || fail "pushed ${NEW:0:9}, but it is not an ancestor of the remote tip ${TIP:0:9}"
    later=0
    while read -r blob path; do
      [ "$(git rev-parse --verify -q "${TIP}:${path}")" = "$blob" ] || { echo "note: a later commit changed $path by tip ${TIP:0:9}"; later=1; }
    done < "$RUN/blobs"
    echo "LANDED ${NEW:0:9} (in tip ${TIP:0:9}); $(wc -l < "$RUN/blobs" | tr -d ' ') landed and $NDEL deleted paths$([ $later = 0 ] && echo ', landed blobs verified at the tip' || echo '; see notes')"
    exit 0
  fi
  echo "push rejected (try $try):"; tail -3 "$RUN/push.log"
  sleep $((try * 3))
done
fail "push not accepted after 8 tries"
