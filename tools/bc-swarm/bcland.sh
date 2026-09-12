#!/usr/bin/env bash
# BC_LANE=<lane> bcland.sh <msgfile> <path>@<source> ... [<path>@DELETE ...] [GroupApproximation.lean@IMPORTS]
# Land additions, modifications and explicit deletions on origin/main through a PRIVATE per-run index, never HEAD, the
# shared index or the working tree. Per-run files live in a fresh mktemp directory under $BC/state, removed on exit;
# concurrent runs share only the append-only per-lane push records $BC/state/pushed-<lane>.txt.
# Base and post-push tip come from `git ls-remote`, objects are fetched by SHA with --no-write-fetch-head, with retries.
# Root imports: `GroupApproximation.lean@IMPORTS` adds `import GroupApproximation.<M>` for every module landed here that
# the base root does not import; `GroupApproximation.lean@<copy>` is accepted only when its diff against the base root
# is exactly added imports of modules landed here. The lines are inserted after the last import line of the fresh
# tip's root at every retry; a deleted or changed root line, or an import of a module not landed here, refuses.
# Shared files: `BC_ACK="<path>=<blob> ..."` declares that your copy of <path> was rebuilt on main's blob <blob> (full
# 40-hex id). An acked path is accepted despite the own-push rule only while main's blob at the landing base still
# equals the acked blob (compare-and-swap); otherwise the landing refuses and names main's current blob. An acked copy
# may remove at most 20 lines of main's version (the truncation / empty-copy class); `BC_ACK_MAXDEL="<path>=<n> ..."`
# raises that limit for an acked path only. The --stat of every acked path is printed.
# Paths under .github/workflows/ need a push credential with the workflow scope; it is checked before any push,
# dry runs included.
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
  grep -qxF "$last" "$PUSHED" || fail "$1 $2 on main and was last written by ${last:0:9}, not by a bcland push of lane $LANE (a shared file needs BC_ACK=$1=<main's blob>)"
}
acked_blob() { awk -v p="$1" '$1 == p { print $2 }' "$RUN/ack"; }
ack_check() {  # ack_check <path> <main blob> <copy blob> <acked blob>
  local path=$1 cur=$2 new=$3 acked=$4 max add del rest
  [ "$cur" = "$acked" ] || fail "$path moved on main: you acked blob ${acked:0:12}, main at ${BASE:0:9} now has $cur; rebuild your change on that blob and ack it"
  max=$(awk -v p="$path" '$1 == p { print $2 }' "$RUN/maxdel"); max=${max:-20}
  git cat-file blob "$cur" > "$RUN/ack.old" || fail "cannot read main's $path"
  git cat-file blob "$new" > "$RUN/ack.new" || fail "cannot read your copy of $path"
  read -r add del rest < <(git diff --no-index --numstat -- "$RUN/ack.old" "$RUN/ack.new" | head -1)
  add=${add:-0}; del=${del:-0}
  echo "ack --stat $path: +$add -$del lines against main blob ${cur:0:12} (max deletions $max)"
  [ "$del" != "-" ] || fail "$path: a binary change cannot be size-checked"
  [ "$del" -le "$max" ] || fail "your copy of $path removes $del lines (max $max); if that is intended, set BC_ACK_MAXDEL=$path=<n>"
}
check_workflow_scope() {
  local tok hdr
  tok=$(gh auth token -u SauersML 2>/dev/null) || fail "cannot read the push credential to check its workflow scope"
  hdr=$(curl -sI -m 20 -H "Authorization: token $tok" https://api.github.com/ 2>/dev/null | tr -d '\r' | grep -i '^x-oauth-scopes:')
  [ -n "$hdr" ] || fail "cannot verify the workflow scope of the push credential (no x-oauth-scopes header); .github/workflows changes need it"
  printf '%s\n' "${hdr#*:}" | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -qx workflow \
    || fail "the push credential lacks the workflow scope (scopes:${hdr#*:}); a push touching .github/workflows would be rejected"
  echo "workflow scope: present in the push credential (scopes:${hdr#*:})"
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
MSG=${1:-}; [ -n "$MSG" ] || fail "usage: BC_LANE=<lane> [BC_ACK=path=blob ...] bcland.sh <msgfile> <path@source | path@DELETE | GroupApproximation.lean@IMPORTS>..."
shift
[ -s "$MSG" ] || fail "empty message file $MSG"
[ $# -ge 1 ] || fail "no paths"
RUN=$(mktemp -d "$STATE/land-$LANE.XXXXXX") || fail "mktemp"
trap 'rm -rf "$RUN"' EXIT
: > "$RUN/ack"; : > "$RUN/maxdel"
for a in ${BC_ACK:-}; do
  p=${a%%=*}; b=${a#*=}
  { [ -n "$p" ] && [ "$p" != "$a" ] && [[ "$b" =~ ^[0-9a-f]{40}$ ]]; } || fail "bad BC_ACK entry '$a' (want <path>=<full 40-hex blob id>)"
  [ "$p" != GroupApproximation.lean ] || fail "BC_ACK cannot name the root; use GroupApproximation.lean@IMPORTS"
  [ -z "$(acked_blob "$p")" ] || fail "BC_ACK names $p twice"
  echo "$p $b" >> "$RUN/ack"
done
for a in ${BC_ACK_MAXDEL:-}; do
  p=${a%%=*}; n=${a#*=}
  { [ -n "$p" ] && [ "$p" != "$a" ] && [[ "$n" =~ ^[0-9]+$ ]]; } || fail "bad BC_ACK_MAXDEL entry '$a' (want <path>=<n>)"
  [ -n "$(acked_blob "$p")" ] || fail "BC_ACK_MAXDEL names $p, which BC_ACK does not ack"
  echo "$p $n" >> "$RUN/maxdel"
done
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
      [ -z "$(acked_blob "$path")" ] || fail "BC_ACK does not apply to deletions ($path)"
      git rev-parse --verify -q "${BASE}:${path}" >/dev/null || fail "cannot delete $path: absent at ${BASE:0:9}"
      own_last "$path" "is being deleted"
      git update-index --force-remove -- "$path" || fail "update-index --force-remove $path"
      NDEL=$((NDEL+1)); echo "$path" >> "$RUN/del"
      continue
    fi
    [ -f "$src" ] || fail "bad spec '$spec': no source file"
    mode=100644; case "$path" in *.sh) mode=100755;; esac
    blob=$(git hash-object -w -- "$src") || fail "hash-object $src"
    acked=$(acked_blob "$path")
    if old=$(git rev-parse --verify -q "${BASE}:${path}"); then
      if [ -n "$acked" ]; then ack_check "$path" "$old" "$blob" "$acked"
      elif [ "$old" != "$blob" ]; then own_last "$path" "differs"; fi
    else
      [ -z "$acked" ] || fail "BC_ACK names $path, which is absent at ${BASE:0:9}"
      NNEW=$((NNEW+1))
    fi
    git update-index --add --cacheinfo "$mode,$blob,$path" || fail "update-index $path"
    echo "$path" >> "$RUN/add"; echo "$blob $path" >> "$RUN/blobs"
  done
  while read -r p _; do
    grep -qxF "$p" "$RUN/add" || fail "BC_ACK names $p, which this landing does not land as a source"
  done < "$RUN/ack"
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
  if grep -qE '^\.github/workflows/' "$RUN/changed" "$RUN/deleted"; then check_workflow_scope; fi
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
