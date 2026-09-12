#!/usr/bin/env bash
# BC_LANE=<lane> bcland.sh <msgfile> <repo-path>@<source-file> ...
# Land additions or modifications of the named paths on origin/main through a PRIVATE per-run index, never HEAD, the
# shared index or the working tree. Every per-run file (index, path lists, diff, push log) lives in a fresh mktemp
# directory under $BC/state that is removed on exit, so concurrent runs share nothing except the append-only
# per-lane push records $BC/state/pushed-<lane>.txt.
# Guards (09-12 wipe):
#  - fetch, rev-parse, read-tree, hash-object, update-index, write-tree and commit-tree must each exit 0;
#  - the base tree must carry GroupApproximation.lean and lake-manifest.json;
#  - after read-tree the private index entry count must equal the base tree entry count;
#  - the new tree's entry count must equal the base count plus the number of genuinely new paths;
#  - `git diff --no-renames --name-status BASE NEW` may name only the given paths, and only as A or M: nothing is deleted;
#  - a path that exists on main with different content is refused unless a bcland push by the SAME lane wrote it last;
#  - the push names refs/heads/main explicitly, and every blob is verified on origin/main afterwards.
set -uo pipefail
REPO=/Users/user/nonsofic_existence
BC=__SCRATCHPAD__/bc
STATE=$BC/state; mkdir -p "$STATE"
TAB=$'\t'
fail() { echo "LAND REFUSED: $1"; exit 1; }
LANE=${BC_LANE:-}
[[ "$LANE" =~ ^[a-z0-9][a-z0-9-]*$ ]] || fail "set BC_LANE=<your lane name>; own-push records are kept per lane"
PUSHED=$STATE/pushed-$LANE.txt
touch "$PUSHED" || fail "cannot create $PUSHED"
MSG=${1:-}; [ -n "$MSG" ] || fail "usage: BC_LANE=<lane> bcland.sh <msgfile> <path@source>..."
shift
[ -s "$MSG" ] || fail "empty message file $MSG"
[ $# -ge 1 ] || fail "no paths"
RUN=$(mktemp -d "$STATE/land-$LANE.XXXXXX") || fail "mktemp"
trap 'rm -rf "$RUN"' EXIT
cd "$REPO" || fail "no repo"
export GIT_INDEX_FILE=$RUN/index
CRED='!f() { echo username=SauersML; echo password=$(gh auth token -u SauersML); }; f'
for try in 1 2 3 4 5 6 7 8; do
  git fetch -q origin main || fail "git fetch"
  BASE=$(git rev-parse --verify -q origin/main) || fail "cannot resolve origin/main"
  for root in GroupApproximation.lean lake-manifest.json; do
    git cat-file -e "${BASE}:${root}" 2>/dev/null || fail "origin/main@${BASE:0:9} lacks $root (gutted tree)"
  done
  N_TREE=$(git ls-tree -r --name-only "$BASE" | wc -l | tr -d ' ')
  rm -f "$GIT_INDEX_FILE"
  git read-tree "$BASE" || fail "read-tree of ${BASE:0:9} exited nonzero"
  N_IDX=$(git ls-files | wc -l | tr -d ' ')
  [ "$N_IDX" = "$N_TREE" ] || fail "private index has $N_IDX entries, base tree has $N_TREE"
  NNEW=0; : > "$RUN/paths"; : > "$RUN/blobs"
  for spec in "$@"; do
    path=${spec%%@*}; src=${spec#*@}
    { [ -n "$path" ] && [ "$path" != "$spec" ] && [ -f "$src" ]; } || fail "bad spec '$spec'"
    mode=100644; case "$path" in *.sh) mode=100755;; esac
    blob=$(git hash-object -w -- "$src") || fail "hash-object $src"
    if old=$(git rev-parse --verify -q "${BASE}:${path}"); then
      if [ "$old" != "$blob" ]; then
        last=$(git log -1 --format=%H "$BASE" -- "$path")
        grep -qxF "$last" "$PUSHED" || fail "$path differs on main and was last written by ${last:0:9}, not by a bcland push of lane $LANE"
      fi
    else
      NNEW=$((NNEW+1))
    fi
    git update-index --add --cacheinfo "$mode,$blob,$path" || fail "update-index $path"
    echo "$path" >> "$RUN/paths"; echo "$blob $path" >> "$RUN/blobs"
  done
  TREE=$(git write-tree) || fail "write-tree"
  N_NEWTREE=$(git ls-tree -r --name-only "$TREE" | wc -l | tr -d ' ')
  [ "$N_NEWTREE" = "$((N_TREE + NNEW))" ] || fail "new tree has $N_NEWTREE entries, expected $((N_TREE + NNEW))"
  NEW=$(git commit-tree "$TREE" -p "$BASE" -F "$MSG") || fail "commit-tree"
  [ -n "$NEW" ] || fail "empty commit id"
  git diff --no-renames --name-status "$BASE" "$NEW" > "$RUN/diff" || fail "diff"
  if grep -vE "^[AM]${TAB}" "$RUN/diff" | grep -q .; then
    fail "commit would delete or retype: $(grep -vE "^[AM]${TAB}" "$RUN/diff" | head -3 | tr '\n' ' ')"
  fi
  cut -f2 "$RUN/diff" | LC_ALL=C sort > "$RUN/changed"
  LC_ALL=C sort -u "$RUN/paths" > "$RUN/want"
  [ -z "$(LC_ALL=C comm -23 "$RUN/changed" "$RUN/want")" ] || fail "commit touches paths outside the given set"
  if [ ! -s "$RUN/changed" ]; then echo "LAND NOOP: every path already on main at ${BASE:0:9}"; exit 0; fi
  echo "candidate ${NEW:0:9} on ${BASE:0:9} (lane $LANE):"; cat "$RUN/diff"
  if git -c credential.helper= -c credential.helper="$CRED" push origin "${NEW}:refs/heads/main" > "$RUN/push.log" 2>&1; then
    echo "$NEW" >> "$PUSHED"
    git fetch -q origin main || fail "post-push fetch"
    TIP=$(git rev-parse origin/main)
    bad=0
    while read -r blob path; do
      [ "$(git rev-parse --verify -q "${TIP}:${path}")" = "$blob" ] || { echo "VERIFY MISMATCH $path"; bad=1; }
    done < "$RUN/blobs"
    [ $bad = 0 ] || fail "pushed ${NEW:0:9} but a blob differs at origin/main ${TIP:0:9}"
    echo "LANDED ${NEW:0:9} (tip ${TIP:0:9}); $(wc -l < "$RUN/blobs" | tr -d ' ') paths verified"
    exit 0
  fi
  echo "push rejected (try $try):"; tail -3 "$RUN/push.log"
  sleep $((try * 3))
done
fail "push not accepted after 8 tries"
