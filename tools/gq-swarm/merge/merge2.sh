#!/bin/bash
# Build two commits on a fresh origin/main through a private index, verify them, and push only when PUSH=1:
#   M1  merge claude/scale-agents-high-impact-erol9w (plain three-way merge; must be conflict-free)
#   R   save the four unlanded SK census files from the shared checkout under wip/sync-2026-09-17/disk/
# A lost push race rebuilds both on the new tip.  Never touches .git/index, HEAD or the working tree.
set -uo pipefail
REPO=/Users/user/nonsofic_existence
S=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/merge
PUSH=${PUSH:-0}
B1=claude/scale-agents-high-impact-erol9w; P1=28fc55683a6a6de5d5ed6466cb26ef2a7a306dca
RESCUE=wip/sync-2026-09-17/disk
# path and the blob prefix inspected on disk; a changed disk copy aborts
CENSUS="metadata/SK_SENTENCE_CENSUS.md:a0ef05a64 metadata/SK_SENTENCE_CENSUS.tsv:6e0308717 metadata/SK_SENTENCE_MAP.tsv:cbbc84d93 metadata/SK_SENTENCE_SUPERSEDED.tsv:ed12f0f54"
cd "$REPO" || exit 1
die() { unset GIT_INDEX_FILE; echo "ABORT: $*" >&2; exit 1; }
for m in msg1.txt msg3.txt; do [ -s "$S/$m" ] || die "missing message $S/$m"; done

build() {
  avail_kb=$(df -k /System/Volumes/Data | awk 'NR==2{print $4}')
  [ "$avail_kb" -gt 1048576 ] || die "disk below 1 GiB free ($avail_kb KB)"
  git fetch -q origin "+refs/heads/main:refs/remotes/origin/main" "+refs/heads/$B1:refs/remotes/origin/$B1" || die "fetch failed"
  [ "$(git rev-parse "refs/remotes/origin/$B1")" = "$P1" ] || die "$B1 moved on origin; re-inspect before merging"
  BASE=$(git rev-parse refs/remotes/origin/main)
  git cat-file -e "${BASE}:GroupApproximation.lean" || die "base has no root module"
  base_count=$(git ls-tree -r "$BASE" | wc -l | tr -d ' ')
  echo "BASE $BASE ($base_count paths)"
  : > "$S/expected.tsv"

  # M1: plain three-way merge.
  mt=$(git merge-tree --write-tree --name-only "$BASE" "$P1"); rc=$?
  [ $rc -eq 0 ] || die "merge 1 conflicts: $mt"
  T1=$(printf '%s\n' "$mt" | head -1)
  M1=$(git commit-tree "$T1" -p "$BASE" -p "$P1" -F "$S/msg1.txt") || die "commit-tree M1"
  [ -n "$M1" ] || die "empty M1"
  printf '%s\t%s\n' "$(git rev-parse "${P1}:notes/swarm-0917/swarm-lanes.js")" notes/swarm-0917/swarm-lanes.js >> "$S/expected.tsv"

  # R: rescue the census files from disk.
  export GIT_INDEX_FILE="$S/private.index"
  rm -f "$GIT_INDEX_FILE"
  git read-tree "$M1" || die "read-tree M1"
  [ "$(git ls-files | wc -l | tr -d ' ')" = "$(git ls-tree -r "$M1" | wc -l | tr -d ' ')" ] || die "private index count mismatch (M1)"
  for pair in $CENSUS; do
    f=${pair%%:*}; pre=${pair##*:}
    t="$RESCUE/$f"
    git cat-file -e "${M1}:$t" 2>/dev/null && die "rescue path exists: $t"
    sha=$(git hash-object -w "$f") || die "hash-object $f"
    case "$sha" in "$pre"*) ;; *) die "disk copy of $f changed since inspection ($sha)" ;; esac
    printf '100644 %s\t%s\n' "$sha" "$t" | git update-index --index-info || die "update-index $t"
    printf '%s\t%s\n' "$sha" "$t" >> "$S/expected.tsv"
  done
  T3=$(git write-tree) || die "write-tree R"
  R=$(git commit-tree "$T3" -p "$M1" -F "$S/msg3.txt") || die "commit-tree R"
  unset GIT_INDEX_FILE
  [ -n "$R" ] || die "empty R"

  # Verify R against BASE: additions only, exactly the expected paths and blobs, library untouched.
  git diff --no-renames --name-status "$BASE" "$R" > "$S/final.status" || die "final diff"
  awk -F'\t' '$1!="A"' "$S/final.status" > "$S/final.nonadd"
  [ -s "$S/final.nonadd" ] && die "final diff has non-additions: $(head -5 "$S/final.nonadd")"
  cut -f2 "$S/final.status" | sort > "$S/final.paths"
  cut -f2 "$S/expected.tsv" | sort > "$S/expected.paths"
  cmp -s "$S/final.paths" "$S/expected.paths" || die "final path set differs from expected"
  while IFS=$'\t' read -r sha t; do
    [ "$(git rev-parse "${R}:$t")" = "$sha" ] || die "blob mismatch at $t"
  done < "$S/expected.tsv"
  want=$(( base_count + $(wc -l < "$S/expected.paths" | tr -d ' ') ))
  [ "$(git ls-tree -r "$R" | wc -l | tr -d ' ')" = "$want" ] || die "tree count is not base + additions ($want)"
  [ -z "$(git diff --name-only "$BASE" "$R" -- GroupApproximation GroupApproximation.lean)" ] || die "library paths touched"
  git log --format='  %h parents=%p | %s' "$BASE..$R" --first-parent
  cat "$S/final.status"
  echo "R $R"
}

attempt=0
while :; do
  attempt=$((attempt + 1))
  [ $attempt -le 15 ] || die "gave up after 15 push attempts"
  build
  if [ "$PUSH" != 1 ]; then echo "DRY RUN OK: built $R on $BASE"; exit 0; fi
  git push origin "$R:refs/heads/main" > "$S/push.$attempt.log" 2>&1; prc=$?
  cat "$S/push.$attempt.log"
  if [ $prc -eq 0 ]; then
    remote=$(git ls-remote origin refs/heads/main | cut -f1)
    [ "$remote" = "$R" ] || die "push exited 0 but origin main is $remote, not $R"
    echo "$R" > "$S/landed.sha"
    echo "LANDED $R (attempt $attempt)"
    exit 0
  fi
  grep -E 'rejected|non-fast-forward|fetch first' "$S/push.$attempt.log" > /dev/null || die "push failed for a reason other than a lost race"
  echo "lost the race; rebuilding on the new tip"
done
