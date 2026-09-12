#!/usr/bin/env bash
# BC_LANE=<lane> bcland.sh <msgfile> <path>@<source> ... [<path>@DELETE ...] [GroupApproximation.lean@IMPORTS]
# Land additions, modifications and explicit deletions on origin/main through a PRIVATE per-run index, never HEAD, the
# shared index or the working tree. Per-run files live in a fresh mktemp directory under $BC/state, removed on exit;
# concurrent runs share only the append-only per-lane push records $BC/state/pushed-<lane>.txt.
# Base and post-push tip come from `git ls-remote`, objects are fetched by SHA with --no-write-fetch-head, with retries.
# Root imports: GroupApproximation.lean is never taken wholesale from a copy. `GroupApproximation.lean@IMPORTS` adds
# `import GroupApproximation.<M>` for every landed module under GroupApproximation/ the base root does not import yet.
# `GroupApproximation.lean@<source>` is accepted only when its diff against the base root is exactly added
# `import GroupApproximation.<M>` lines for modules landed in this same landing. Either way the lines are inserted
# after the last import line of the fresh tip's root at every retry, so they merge onto the tip. The own-push rule
# does not apply to the root; a deleted or changed root line, or an import of a module not landed here, refuses.
# Guards (09-12 wipe, 09-12 dangling import):
#  - rev-parse, read-tree, hash-object, update-index, write-tree and commit-tree must each exit 0;
#  - the base tree must carry GroupApproximation.lean and lake-manifest.json;
#  - after read-tree the private index entry count must equal the base tree entry count;
#  - the new tree's entry count must equal the base count plus new paths minus deleted paths;
#  - `git diff --no-renames --name-status BASE NEW` may name only the given paths: A or M for sources, D for deletions;
#  - any other path that differs on main, or is deleted, must have been written last by a bcland push of the SAME lane;
#  - bcimportguard.sh on the commit being pushed: no deleted Lean module may still be imported outside wip/;
#  - the push names refs/heads/main; afterwards the pushed commit must be an ancestor of the remote tip.
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
own_last() {
  local last; last=$(git log -1 --format=%H "$BASE" -- "$1")
  grep -qxF "$last" "$PUSHED" || fail "$1 $2 on main and was last written by ${last:0:9}, not by a bcland push of lane $LANE"
}
root_imports() {  # $1 = IMPORTS or a root source file; runs after every other spec is staged
  local spec=$1 L nb ni line blob drc
  git cat-file blob "${BASE}:GroupApproximation.lean" > "$RUN/root.base" || fail "cannot read the root at ${BASE:0:9}"
  sed -n 's|^GroupApproximation/\(.*\)\.lean$|GroupApproximation/\1|p' "$RUN/add" | tr '/' '.' | LC_ALL=C sort -u > "$RUN/landed-mods"
  : > "$RUN/root.ins"
  if [ "$spec" = IMPORTS ]; then
    while IFS= read -r m; do
      grep -qxF "import $m" "$RUN/root.base" || echo "import $m" >> "$RUN/root.ins"
    done < "$RUN/landed-mods"
  else
    [ -f "$spec" ] || fail "root source $spec is missing"
    diff "$RUN/root.base" "$spec" > "$RUN/root.diff"; drc=$?
    [ $drc -le 1 ] || fail "diff of the root source against the base root exited $drc"
    if grep -q '^<' "$RUN/root.diff"; then
      fail "the root source deletes or changes lines of the root at ${BASE:0:9}: $(grep -m2 '^<' "$RUN/root.diff" | tr '\n' ' ')(pass GroupApproximation.lean@IMPORTS instead of a copy)"
    fi
    sed -n 's/^> //p' "$RUN/root.diff" > "$RUN/root.ins"
    while IFS= read -r line; do
      [[ "$line" =~ ^import\ (GroupApproximation\.[A-Za-z0-9_.]+)$ ]] || fail "the root source adds a line that is not a plain GroupApproximation import: '$line'"
      grep -qxF "${BASH_REMATCH[1]}" "$RUN/landed-mods" || fail "root source imports ${BASH_REMATCH[1]}, which this landing does not land"
      if grep -qxF "$line" "$RUN/root.base"; then fail "the root source adds '$line', which the root already has"; fi
    done < "$RUN/root.ins"
  fi
  [ -s "$RUN/root.ins" ] || { echo "root: nothing to add"; return 0; }
  [ -z "$(LC_ALL=C sort "$RUN/root.ins" | uniq -d)" ] || fail "a root import line is added twice"
  L=$(grep -n '^import ' "$RUN/root.base" | tail -1 | cut -d: -f1)
  [ -n "$L" ] || fail "the base root has no import line to anchor on"
  { head -n "$L" "$RUN/root.base"; cat "$RUN/root.ins"; tail -n +"$((L + 1))" "$RUN/root.base"; } > "$RUN/root.new"
  nb=$(wc -l < "$RUN/root.base" | tr -d ' '); ni=$(wc -l < "$RUN/root.ins" | tr -d ' ')
  [ "$(wc -l < "$RUN/root.new" | tr -d ' ')" = "$((nb + ni))" ] || fail "rebuilt root has the wrong line count"
  diff "$RUN/root.base" "$RUN/root.new" > "$RUN/root.check"
  { ! grep -q '^<' "$RUN/root.check" && [ "$(grep -c '^>' "$RUN/root.check")" = "$ni" ]; } \
    || fail "rebuilt root is not the base root plus exactly the added import lines"
  blob=$(git hash-object -w -- "$RUN/root.new") || fail "hash-object of the rebuilt root"
  git update-index --add --cacheinfo "100644,$blob,GroupApproximation.lean" || fail "update-index of the root"
  echo "GroupApproximation.lean" >> "$RUN/add"; echo "$blob GroupApproximation.lean" >> "$RUN/blobs"
  echo "root: adding $ni import line(s) after line $L of the root at ${BASE:0:9}: $(tr '\n' ' ' < "$RUN/root.ins")"
}
LANE=${BC_LANE:-}
[[ "$LANE" =~ ^[a-z0-9][a-z0-9-]*$ ]] || fail "set BC_LANE=<your lane name>; own-push records are kept per lane"
[ -f "$GUARD" ] || fail "import guard $GUARD is missing"
PUSHED=$STATE/pushed-$LANE.txt
touch "$PUSHED" || fail "cannot create $PUSHED"
MSG=${1:-}; [ -n "$MSG" ] || fail "usage: BC_LANE=<lane> bcland.sh <msgfile> <path@source | path@DELETE | GroupApproximation.lean@IMPORTS>..."
shift
[ -s "$MSG" ] || fail "empty message file $MSG"
[ $# -ge 1 ] || fail "no paths"
RUN=$(mktemp -d "$STATE/land-$LANE.XXXXXX") || fail "mktemp"
trap 'rm -rf "$RUN"' EXIT
cd "$REPO" || fail "no repo"
export GIT_INDEX_FILE=$RUN/index
CRED='!f() { echo username=SauersML; echo password=$(gh auth token -u SauersML); }; f'
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
  NNEW=0; NDEL=0; ROOTSPEC=""; : > "$RUN/add"; : > "$RUN/del"; : > "$RUN/blobs"
  for spec in "$@"; do
    path=${spec%%@*}; src=${spec#*@}
    { [ -n "$path" ] && [ "$path" != "$spec" ]; } || fail "bad spec '$spec'"
    if [ "$path" = GroupApproximation.lean ]; then
      [ "$src" != DELETE ] || fail "the root file cannot be deleted"
      [ -z "$ROOTSPEC" ] || fail "GroupApproximation.lean is given twice"
      ROOTSPEC=$src; continue
    fi
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
  [ -z "$ROOTSPEC" ] || root_imports "$ROOTSPEC"
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
