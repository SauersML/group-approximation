#!/bin/bash
# gkland.sh <lane> <msgfile> <spec> [<spec>...]
#
# Land exactly the given paths on origin/main with a private index (never the shared
# index, HEAD, or working tree), retrying against a moving main.
#
#   spec = repo/relative/path              lands the shared checkout's disk copy of that path
#        | repo/relative/path@/abs/file    lands the content of /abs/file at that repo path
#        | repo/relative/path@DELETE       removes that path from main
#
# Guards, per path, against the tip at push time:
#   NEW        path absent on main
#   SAME       main already holds this content
#   OVERWRITE  main's blob is the one this lane last pushed
#   MERGED     GK_ACK="path=<origin blob> ..." says you merged onto (or retire) that exact blob
#   DELETE     removal of a blob this lane last pushed, or of an acked blob
#   REFUSE     anything else: someone else changed it; re-read, merge, set GK_ACK, rerun
# Lint on research/*.md nodes: id == filename, id <= 64 chars, kind claim|route,
# requires/target/distinct_from/refuted_by name existing claims, invalidates names routes;
# a deleted node's id must not be named by any remaining node.
# GK_DRYRUN=1 builds and lints the commit but does not push. GK_NOLINT=1 skips the lint
# (say why in the commit message).
# Exit: 0 landed or nothing to land, 1 error or gave up, 2 refused, 3 lint failed, 64 usage.
#
# 2026-09-12 fixes: the auth check matched commit SHAs containing "403" (reported by
# gk-rokhlin) and now matches only genuine auth messages; @DELETE specs added.
set -u
SP=/private/tmp/claude-501/-Users-user-nonsofic-existence/0a930a1d-0cf3-4aa0-b91a-b8bfce7d68c7/scratchpad/gk
R=/Users/user/nonsofic_existence
LANE="${1:-}"; MSG="${2:-}"
[ -n "$LANE" ] && [ -n "$MSG" ] || { echo "usage: gkland.sh <lane> <msgfile> <spec>..."; exit 64; }
shift 2
[ "$#" -ge 1 ] || { echo "NO PATHS"; exit 64; }
[ -s "$MSG" ] || { echo "NO MSG FILE: $MSG"; exit 64; }
mkdir -p "$SP/state"
REC="$SP/state/pushed-$LANE.tsv"; touch "$REC"
WORK="$SP/state/work-$LANE-$$"; mkdir -p "$WORK"
SPECS="$WORK/specs.tsv"; : > "$SPECS"
cd "$R" || exit 1

for s in "$@"; do
  case "$s" in
    *@DELETE) p="${s%@DELETE}"; src=DELETE ;;
    *@/*)     p="${s%%@/*}"; src="/${s#*@/}" ;;
    *)        p="$s"; src="$R/$s" ;;
  esac
  case "$p" in /*|../*|*/../*|"") echo "BAD REPO PATH: '$p'"; exit 64 ;; esac
  if [ "$src" = DELETE ]; then
    b=DELETE
  else
    [ -f "$src" ] || { echo "MISSING SOURCE: $src"; exit 64; }
    b=$(git hash-object -w -- "$src") || { echo "HASH FAIL $src"; exit 1; }
    [ -n "$b" ] || { echo "EMPTY HASH $src"; exit 1; }
  fi
  printf '%s\t%s\t%s\n' "$p" "$b" "$src" >> "$SPECS"
done
cut -f1 "$SPECS" | sort -u > "$WORK/paths.txt"
[ "$(wc -l < "$WORK/paths.txt")" -eq "$(wc -l < "$SPECS")" ] || { echo "DUPLICATE PATH IN SPECS"; exit 64; }

guard() {
  local T="$1" bad=0 p b src ob last acked
  while IFS=$'\t' read -r p b src; do
    if git cat-file -e "${T}:${p}" 2>/dev/null; then
      ob=$(git rev-parse "${T}:${p}")
      last=$(awk -F'\t' -v p="$p" '$1==p{x=$2} END{print x}' "$REC")
      acked=0; printf ' %s ' "${GK_ACK:-}" | grep -qF " ${p}=${ob} " && acked=1
      if [ "$b" = DELETE ]; then
        if [ -n "$last" ] && [ "$ob" = "$last" ]; then echo "  DELETE    $p (own last push)"
        elif [ "$acked" = 1 ]; then echo "  DELETE    $p (acked origin blob ${ob:0:10})"
        else
          echo "  REFUSE    $p: deleting main's blob ${ob:0:10}, which is not your last push."
          echo "            Read it (gkshow.sh), then rerun with GK_ACK=\"${p}=${ob}\""
          bad=1
        fi
      elif [ "$ob" = "$b" ]; then echo "  SAME      $p"
      elif [ -n "$last" ] && [ "$ob" = "$last" ]; then echo "  OVERWRITE $p (own last push)"
      elif [ "$acked" = 1 ]; then echo "  MERGED    $p (onto origin blob ${ob:0:10})"
      else
        echo "  REFUSE    $p: main's blob ${ob:0:10} is not your last push."
        echo "            Fetch it (gkshow.sh), merge your change into it, then rerun with GK_ACK=\"${p}=${ob}\""
        bad=1
      fi
    else
      if [ "$b" = DELETE ]; then echo "  ABSENT    $p (already not on main)"; else echo "  NEW       $p"; fi
    fi
  done < "$SPECS"
  return $bad
}

fm() {  # frontmatter of <rev>:<path>
  git show "$1" 2>/dev/null | awk 'NR==1 && $0!="---" {exit} NR==1 {next} $0=="---" {exit} {print}'
}
kind_of() {  # <rev> <id>
  fm "${1}:research/${2}.md" | awk '/^kind:/ {sub(/^kind:[ ]*/, ""); sub(/[ ]+$/, ""); print; exit}'
}
refs() {  # frontmatter on stdin; print the ids under key $1
  awk -v k="$1" '
    BEGIN { inb = 0 }
    index($0, k ":") == 1 {
      v = substr($0, length(k) + 2); sub(/^[ ]+/, "", v); sub(/[ ]+$/, "", v)
      if (v ~ /^\[/) { gsub(/[\[\]]/, "", v); n = split(v, a, ","); for (i = 1; i <= n; i++) { x = a[i]; gsub(/^[ ]+|[ ]+$/, "", x); if (x != "") print x }; inb = 0; next }
      if (v == "") { inb = 1; next }
      print v; inb = 0; next
    }
    inb && /^[ ]+- / { x = $0; sub(/^[ ]+- +/, "", x); sub(/[ ]+$/, "", x); print x; next }
    inb && /^[ ]+[a-z0-9][a-z0-9-]*:/ { x = $0; sub(/^[ ]+/, "", x); sub(/:.*/, "", x); print x; next }
    inb && /^[^ ]/ { inb = 0 }
  '
}
lint() {
  local N="$1" bad=0 p b src base F id kd key want r rk hits
  while IFS=$'\t' read -r p b src; do
    case "$p" in research/artifacts/*|research/FRONTIER.md) continue ;; research/*.md) ;; *) continue ;; esac
    base=$(basename "$p" .md)
    if [ "$b" = DELETE ]; then
      hits=$(git grep -l -E "(^|[^a-z0-9-])${base}([^a-z0-9-]|\$)" "$N" -- 'research/*.md' 2>/dev/null | sed "s/^${N}://" | grep -v '^research/artifacts/' | grep -v '^research/FRONTIER.md$')
      if [ -n "$hits" ]; then echo "  LINT $p: deleted id '$base' is still named by: $(echo $hits)"; bad=1; fi
      continue
    fi
    F=$(fm "${N}:${p}")
    id=$(printf '%s\n' "$F" | awk '/^id:/ {sub(/^id:[ ]*/, ""); sub(/[ ]+$/, ""); print; exit}')
    kd=$(printf '%s\n' "$F" | awk '/^kind:/ {sub(/^kind:[ ]*/, ""); sub(/[ ]+$/, ""); print; exit}')
    [ "$id" = "$base" ] || { echo "  LINT $p: id '$id' does not equal the filename"; bad=1; }
    [ "${#base}" -le 64 ] || { echo "  LINT $p: id is ${#base} chars, cap is 64"; bad=1; }
    case "$kd" in claim|route) ;; *) echo "  LINT $p: kind '$kd' is not claim or route"; bad=1 ;; esac
    for key in requires target distinct_from refuted_by invalidates; do
      want=claim; [ "$key" = invalidates ] && want=route
      for r in $(printf '%s\n' "$F" | refs "$key"); do
        rk=$(kind_of "$N" "$r")
        if [ -z "$rk" ]; then echo "  LINT $p: $key names '$r', which is not on main or in this landing"; bad=1
        elif [ "$rk" != "$want" ]; then echo "  LINT $p: $key names '$r', a $rk (want a $want)"; bad=1
        fi
      done
    done
    if [ "$kd" = claim ] && ! git show "${N}:${p}" | grep -q '^## Attempts'; then
      if ! git grep -q -E "^target: ${base}[ ]*\$" "$N" -- 'research/*.md'; then
        echo "  WARN $p: claim has no route into it and no '## Attempts' section (cairn check --changed errors on that)"
      fi
    fi
  done < "$SPECS"
  return $bad
}

TOK=$(gh auth token --user SauersML 2>/dev/null || true)
export GK_TOK="$TOK"
push_new() {
  if [ -n "$GK_TOK" ]; then
    git -c credential.helper= -c 'credential.helper=!f(){ test "$1" = get && { echo username=SauersML; echo "password=$GK_TOK"; }; };f' push origin "${1}:refs/heads/main"
  else
    git push origin "${1}:refs/heads/main"
  fi
}

LINTED=0
for attempt in $(seq 1 40); do
  T=$(git ls-remote origin refs/heads/main 2>/dev/null | cut -f1)
  if [ -z "$T" ]; then echo "ls-remote failed (attempt $attempt)"; sleep 2; continue; fi
  git cat-file -e "${T}^{commit}" 2>/dev/null || git fetch -q origin "$T" 2>/dev/null || git fetch -q origin main 2>/dev/null
  if ! git cat-file -e "${T}^{commit}" 2>/dev/null; then echo "cannot fetch ${T:0:10} (attempt $attempt)"; sleep 1; continue; fi
  echo "attempt $attempt: base ${T:0:10}"
  guard "$T" || { echo "REFUSED. Nothing pushed."; exit 2; }
  export GIT_INDEX_FILE="$WORK/index"; rm -f "$GIT_INDEX_FILE"
  if ! git read-tree "$T"; then unset GIT_INDEX_FILE; echo "read-tree failed"; exit 1; fi
  while IFS=$'\t' read -r p b src; do
    if [ "$b" = DELETE ]; then
      git update-index --force-remove -- "$p" || { unset GIT_INDEX_FILE; echo "remove failed for $p"; exit 1; }
    else
      git update-index --add --cacheinfo "100644,${b},${p}" || { unset GIT_INDEX_FILE; echo "update-index failed for $p"; exit 1; }
    fi
  done < "$SPECS"
  TREE=$(git write-tree); unset GIT_INDEX_FILE
  [ -n "$TREE" ] || { echo "write-tree failed"; exit 1; }
  NEW=$(git commit-tree "$TREE" -p "$T" -F "$MSG")
  [ -n "$NEW" ] || { echo "commit-tree failed (EMPTY NEW)"; exit 1; }
  git diff --name-only "$T" "$NEW" | sort > "$WORK/changed.txt"
  stray=$(comm -23 "$WORK/changed.txt" "$WORK/paths.txt")
  [ -z "$stray" ] || { echo "STRAY PATHS, nothing pushed: $stray"; exit 1; }
  if [ ! -s "$WORK/changed.txt" ]; then echo "NOTHING TO LAND: main already holds every path"; rm -rf "$WORK"; exit 0; fi
  if [ "$LINTED" = 0 ] && [ "${GK_NOLINT:-0}" != 1 ]; then
    lint "$NEW" || { echo "LINT FAILED. Nothing pushed; fix the nodes and rerun."; exit 3; }
    LINTED=1
  fi
  if [ "${GK_DRYRUN:-0}" = 1 ]; then
    echo "DRYRUN: would push ${NEW:0:10} changing: $(tr '\n' ' ' < "$WORK/changed.txt")"
    git show --stat --format='%s' "$NEW" | head -20
    rm -rf "$WORK"; exit 0
  fi
  if push_new "$NEW" > "$WORK/push.log" 2>&1; then
    while IFS=$'\t' read -r p b src; do
      printf '%s\t%s\n' "$p" "$b" >> "$REC"
      if [ "$b" != DELETE ] && [ "$src" = "$R/$p" ] && [ "$(git hash-object -- "$p" 2>/dev/null)" = "$b" ]; then
        git update-index --add -- "$p" 2>/dev/null
      fi
    done < "$SPECS"
    echo "LANDED ${NEW:0:10} on main (attempt $attempt): $(tr '\n' ' ' < "$WORK/changed.txt")"
    rm -rf "$WORK"; exit 0
  fi
  if grep -qE "Permission to [^ ]+ denied|denied to [A-Za-z0-9_-]+|The requested URL returned error: 403|HTTP 403|could not read Username|Authentication failed|Invalid username or password" "$WORK/push.log"; then
    echo "AUTH FAILURE:"; cat "$WORK/push.log"; exit 1
  fi
  sleep "0.$((RANDOM % 9 + 1))"
done
echo "GAVE UP after 40 attempts; nothing landed. Rerun."
exit 1
