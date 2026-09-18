#!/usr/bin/env bash
# Serialized, batching lander: put verified results on main without touching
# anyone's working tree.
#
#   tools/cairn-land.sh -m SUBJECT [-F BODY_FILE] [--mirror BRANCH] [--node ID] SRC PATH...
#
# SRC is the worktree the result lives in; each PATH is relative to it. The
# request is spooled, then the lander takes a lock shared by every worktree in
# the container. Whoever holds the lock lands every pending request (up to
# CAIRN_LAND_BATCH, default 32): it builds a temporary worktree at origin/main,
# copies all their paths in, regenerates the frontier with `bin/cairn check`
# once (exit 0 required), and makes one commit per request. If the batch fails
# the check, it is bisected: each half is re-checked on top of whatever already
# passed, down to single requests, so only the failing ones get exit 4 and one
# bad request costs about 2*log2(batch) checks. A request file that differs from
# main's is merged, not copied over it: the lander finds the past version of the
# file the request was copied from and three-way merges, so edits other agents
# landed on the same file since then are kept, and a stale unedited copy lands
# nothing. Conflicting edits fail that request with exit 4. One push lands the batch. A
# rejected push whose new main commits touch nothing the check reads (research,
# notes, tools, bin, or a deletion or rename anywhere) is replayed onto the new
# main and pushed again at once, with no check. So is one whose new main commits
# touch neither tools, bin, any landed path, nor delete or rename anything: the
# passing requests are re-committed on the new main without a check (at most 30
# times), keeping main's FRONTIER.md for the next check to refresh, because a
# check on a busy main loses the race every time. Any other rejected push resets to
# the new origin/main and rebuilds only the requests that passed (one check), so
# the generated research/FRONTIER.md never conflicts and a busy main cannot
# livelock it. It never force-pushes. A waiter whose request was landed by another holder prints that
# holder's result and exits with its code.
#
# Trailers come from $CAIRN_LAND_TRAILERS (a file whose lines are appended to
# the message). --mirror pushes the landed head to BRANCH only as a
# fast-forward. On success a `landed` event goes to the cairn-live feed.
set -euo pipefail

subject="" body_file="" mirror="" node="" remote="${CAIRN_LAND_REMOTE:-origin}"
while [ $# -gt 0 ]; do
  case "$1" in
    -m) subject="$2"; shift 2 ;;
    -F) body_file="$2"; shift 2 ;;
    --mirror) mirror="$2"; shift 2 ;;
    --node) node="$2"; shift 2 ;;
    --) shift; break ;;
    -*) echo "unknown option $1" >&2; exit 64 ;;
    *) break ;;
  esac
done
[ -n "$subject" ] && [ $# -ge 2 ] || { sed -n '2,22p' "$0" >&2; exit 64; }
src="$(cd "$1" && pwd)"; shift
paths=("$@")

root="$(cd "$(dirname "$0")/.." && pwd)"
for p in "${paths[@]}"; do
  case "$p" in /*|*..*|*$'\n'*) echo "path must be relative and inside SRC: $p" >&2; exit 64 ;; esac
  [ -e "$src/$p" ] || { echo "missing in $src: $p" >&2; exit 4; }
done

state="${CAIRN_LIVE:-$(CAIRN_ROOT="$root" python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); import cairn, os; print(os.path.join(cairn.shared_dir(), "live"))' "$root/tools")}"
spool="$state/land-queue"
mkdir -p "$spool"

# Spool the request atomically: a directory appears only once it is complete.
req="$spool/$(date +%s%N)-$$"
mkdir "$req.tmp"
{
  printf '%s\n' "$subject"
  if [ -n "$body_file" ]; then printf '\n'; cat "$body_file"; fi
  if [ -n "${CAIRN_LAND_TRAILERS:-}" ]; then printf '\n'; cat "$CAIRN_LAND_TRAILERS"; fi
} >"$req.tmp/msg"
printf '%s\n' "$src" >"$req.tmp/src"
printf '%s\n' "${paths[@]}" >"$req.tmp/paths"
printf '%s\n' "$node" >"$req.tmp/node"
printf '%s\n' "${CAIRN_AGENT:-lander}" >"$req.tmp/agent"
printf '%s\n' "$subject" >"$req.tmp/subject"
mv "$req.tmp" "$req"

finish_own() {  # print the result recorded for this request and exit with its code
  cat "$req/out" >&2
  local code; code="$(cat "$req/code")"
  rm -rf "$req"
  exit "$code"
}

exec 9>"$state/land.lock"
echo "waiting for the land lock ($state/land.lock)" >&2
flock 9
[ -f "$req/code" ] && finish_own

wt="$(mktemp -d)"; rmdir "$wt"
cleanup() { git -C "$root" worktree remove --force "$wt" >/dev/null 2>&1 || true; rm -rf "$wt" "$wt.check.log" "$wt.frontier" "$wt.changed"; }
trap cleanup EXIT

# Pending requests, oldest first; our own is always included.
batch=()
while IFS= read -r d; do batch+=("$spool/$d"); done < <(
  ls -1 "$spool" | grep -Ev '\.tmp$' | while IFS= read -r d; do
    [ -f "$spool/$d/code" ] || [ ! -f "$spool/$d/msg" ] || printf '%s\n' "$d"
  done | sort | head -n "${CAIRN_LAND_BATCH:-32}")
case " ${batch[*]} " in *" $req "*) ;; *) batch+=("$req") ;; esac
echo "landing a batch of ${#batch[@]} request(s)" >&2

merge_in() {  # put one request file at path $2, merging main's newer edits instead of overwriting them
  local f="$1" p="$2" c b best="" bestdel=-1 del
  mkdir -p "$wt/$(dirname "$p")"
  if [ -L "$f" ] || [ -L "$wt/$p" ] || [ ! -f "$wt/$p" ] || cmp -s "$f" "$wt/$p" ||
    [ "$p" = research/FRONTIER.md ] || ! grep -Iq . "$f" || ! grep -Iq . "$wt/$p"; then
    cp -a "$f" "$wt/$p"; return 0
  fi
  # The request was copied from some past version of the file: take the one it
  # removes the fewest lines from (newest on ties) as the base of a three-way merge.
  b="$(mktemp)"
  for c in $(git -C "$wt" log --format=%H -n 30 HEAD -- "$p"); do
    git -C "$wt" show "$c:$p" >"$b" 2>/dev/null || continue
    del="$(diff "$b" "$f" | grep -c '^<' || true)"
    if [ "$bestdel" = -1 ] || [ "$del" -lt "$bestdel" ]; then best="$c" bestdel="$del"; fi
    [ "$del" = 0 ] && break
  done
  # No history (the file is only in this batch so far): the request's copy wins.
  [ -n "$best" ] || { rm -f "$b"; cp -a "$f" "$wt/$p"; return 0; }
  git -C "$wt" show "$best:$p" >"$b"
  if git merge-file -q -p "$f" "$b" "$wt/$p" >"$wt/$p.merged" 2>/dev/null ||
    # Both sides only added text at the same spot (typically a new section at the
    # end of a shared root): keep both, the request's first.
    { { git merge-file -q -p --diff3 "$f" "$b" "$wt/$p" 2>/dev/null || true; } |
        awk '/^\|\|\|\|\|\|\| /{inb=1; next} /^=======$/{inb=0} inb{bad=1} END{exit bad}' &&
      git merge-file -q -p --union "$f" "$b" "$wt/$p" >"$wt/$p.merged" 2>/dev/null; }; then
    mv "$wt/$p.merged" "$wt/$p"; rm -f "$b"; return 0
  fi
  rm -f "$b" "$wt/$p.merged"
  echo "$p changed on $remote/main since this request copied it ($(git -C "$wt" log --format=%h -n 1 HEAD -- "$p")), and the edits conflict: re-copy it from $remote/main, reapply, resubmit" >"$r_cur/out"
  return 1
}

copy_in() {  # copy one request's paths into the worktree
  local r="$1" s p f
  s="$(cat "$r/src")"; r_cur="$r"
  while IFS= read -r p; do
    [ -e "$s/$p" ] || { echo "missing in $s: $p" >"$r/out"; return 1; }
    if [ -d "$s/$p" ]; then
      while IFS= read -r f; do merge_in "$s/$p/$f" "$p/$f" || return 1; done < <(cd "$s/$p" && find . \( -type f -o -type l \) | sed 's#^\./##')
    else
      merge_in "$s/$p" "$p" || return 1
    fi
  done <"$r/paths"
}

check() { (cd "$wt" && bin/cairn check >"$wt.check.log" 2>&1); }

reset_wt() { git -C "$wt" reset -q --hard HEAD; git -C "$wt" clean -qfd; }

commit_req() {  # commit one request's paths; prints nothing, sets status files
  local r="$1" p
  while IFS= read -r p; do git -C "$wt" add -- "$p"; done <"$r/paths"
  if git -C "$wt" diff --cached --quiet; then
    echo "nothing to land: origin/main already has these paths" >"$r/out.pending"
    echo 0 >"$r/code.pending"
  else
    git -C "$wt" commit -q -F "$r/msg"
    git -C "$wt" rev-parse HEAD >"$r/sha"
  fi
}

land_set() {  # check these requests on top of HEAD; commit them if they pass, else bisect
  [ $# = 0 ] && return 0
  local r h ok=() bad=0
  for r in "$@"; do
    if copy_in "$r"; then ok+=("$r"); else mv "$r/out" "$r/out.pending"; echo 4 >"$r/code.pending"; bad=1; fi
  done
  # A request that no longer merges onto this main may have half-copied: drop it and start over.
  if [ "$bad" = 1 ]; then reset_wt; land_set ${ok[@]+"${ok[@]}"}; return 0; fi
  if check; then
    # Re-apply the requests one at a time (the same merges, in the same order, so
    # the same tree), committing each, so every commit carries only its own edits.
    [ -f "$wt/research/FRONTIER.md" ] && cp "$wt/research/FRONTIER.md" "$wt.frontier"
    reset_wt
    for r in "$@"; do
      copy_in "$r" || true
      [ -f "$wt.frontier" ] && { cp "$wt.frontier" "$wt/research/FRONTIER.md"; git -C "$wt" add research/FRONTIER.md; }
      commit_req "$r"; good+=("$r")
    done
    rm -f "$wt.frontier"
    return 0
  fi
  reset_wt
  if [ $# = 1 ]; then
    { echo "bin/cairn check failed on origin/main + these paths; nothing pushed"; tail -40 "$wt.check.log"; } >"$1/out.pending"
    echo 4 >"$1/code.pending"
    return 0
  fi
  h=$(($# / 2))
  land_set "${@:1:h}"
  land_set "${@:h+1}"
}

outside_graph() {  # true if main moved from $1 to $2 without touching anything the check reads
  git -C "$root" diff --quiet "$1" "$2" -- research notes tools bin &&
    [ -z "$(git -C "$root" diff --name-only --diff-filter=DR "$1" "$2")" ]
}

disjoint_graph() {  # true if main moved from $1 to $2 without touching the checker, a landed path, or deleting anything
  local r p
  git -C "$root" diff --quiet "$1" "$2" -- tools bin || return 1
  [ -z "$(git -C "$root" diff --name-only --diff-filter=DR "$1" "$2")" ] || return 1
  git -C "$root" diff --name-only "$1" "$2" >"$wt.changed"
  for r in "${good[@]}"; do
    [ -f "$r/sha" ] || continue
    while IFS= read -r p; do
      awk -v p="${p%/}" '$0 == p || index($0, p "/") == 1 { hit = 1 } END { exit !hit }' "$wt.changed" && return 1
    done <"$r/paths"
  done
  return 0
}

landed="" good=() live=() base="" rebuild=1 checks=0 replays=0
for r in "${batch[@]}"; do rm -f "$r/sha" "$r/out.pending" "$r/code.pending"; done
for attempt in $(seq 1 200); do
  if [ "$rebuild" = 1 ]; then
    checks=$((checks + 1))
    [ "$checks" -gt 20 ] && break
    git -C "$root" fetch -q "$remote" main
    git -C "$root" worktree remove --force "$wt" >/dev/null 2>&1 || true
    rm -rf "$wt"
    base="$(git -C "$root" rev-parse "$remote/main")"
    git -C "$root" worktree add -q --detach "$wt" "$base"

    if [ "$checks" = 1 ]; then
      # Requests whose paths vanished fail at once; the rest are bisected.
      for r in "${batch[@]}"; do
        if copy_in "$r"; then live+=("$r"); else echo 4 >"$r/code.pending"; mv "$r/out" "$r/out.pending"; fi
      done
      reset_wt
    else
      # A rejected push means main moved, not that the verdicts changed: keep the
      # failures, and rebuild only the requests that passed, so a retry costs one
      # check instead of the whole bisection and can win the race against other pushers.
      live=("${good[@]}")
      for r in "${live[@]}"; do rm -f "$r/sha" "$r/out.pending" "$r/code.pending"; done
    fi
    good=()
    land_set ${live[@]+"${live[@]}"}

    n=0; for r in "${good[@]}"; do [ -f "$r/sha" ] && n=$((n + 1)); done
    if [ "$n" = 0 ]; then landed="none"; break; fi
  fi

  # Record every landed sha from the log.
  shas=(); while IFS= read -r s; do shas+=("$s"); done < <(git -C "$wt" rev-list --reverse "$base..HEAD")
  i=0; for r in "${good[@]}"; do [ -f "$r/sha" ] && { printf '%s\n' "${shas[$i]}" >"$r/sha"; i=$((i + 1)); }; done
  if git -C "$wt" push -q "$remote" HEAD:main; then
    landed="$(git -C "$wt" rev-parse HEAD)"
    break
  fi
  # Main moved. If it moved only outside the graph (research, notes, the tools,
  # and no deletions or renames anywhere), the verdicts and the generated
  # frontier still hold: replay the commits on the new main and push again at
  # once, which wins against pushers far faster than a check. Otherwise rebuild.
  git -C "$root" fetch -q "$remote" main
  new="$(git -C "$root" rev-parse "$remote/main")"
  if outside_graph "$base" "$new" && git -C "$wt" rebase -q --onto "$new" "$base" >/dev/null 2>&1 &&
    [ "$(git -C "$wt" rev-list --count "$new..HEAD")" = "${#shas[@]}" ]; then
    echo "push rejected (attempt $attempt); main moved outside the graph, replaying on the new $remote/main" >&2
    base="$new" rebuild=0
  elif [ "$replays" -lt 30 ] && disjoint_graph "$base" "$new"; then
    # Main moved in other research files only. A fresh check would lose the race
    # again on a busy main, so re-commit the passing requests on the new main
    # without one; its FRONTIER.md is kept and the next check refreshes it.
    git -C "$wt" rebase --abort >/dev/null 2>&1 || true
    echo "push rejected (attempt $attempt); main moved in disjoint research, re-committing on the new $remote/main" >&2
    replays=$((replays + 1))
    git -C "$wt" reset -q --hard "$new"; git -C "$wt" clean -qfd
    base="$new" rebuild=0 again=()
    for r in "${good[@]}"; do [ -f "$r/sha" ] && again+=("$r"); done
    for r in "${again[@]}"; do
      rm -f "$r/sha"
      copy_in "$r" || { rebuild=1; break; }
      commit_req "$r"
    done
    n=0; for r in "${good[@]}"; do [ -f "$r/sha" ] && n=$((n + 1)); done
    [ "$rebuild" = 0 ] && [ "$n" = 0 ] && { landed="none"; break; }
  else
    git -C "$wt" rebase --abort >/dev/null 2>&1 || true
    echo "push rejected (attempt $attempt); rebuilding the passing requests on the new $remote/main" >&2
    rebuild=1
    sleep 1
  fi
done

if [ -z "$landed" ]; then
  echo "could not land after $attempt attempts ($checks checks)" >&2
  exit 1  # our own request stays spooled; the next holder retries it
fi

for r in "${batch[@]}"; do
  if [ -f "$r/sha" ]; then
    echo "landed $(cat "$r/sha") on $remote/main" >"$r/out"; echo 0 >"$r/code.tmp"
    rnode="$(cat "$r/node")"
    CAIRN_ROOT="$root" CAIRN_LIVE="$state" CAIRN_AGENT="$(cat "$r/agent")" \
      python3 "$root/tools/cairn_live.py" landed ${rnode:+--node "$rnode"} \
      --text "$(cat "$r/subject") ($(cat "$r/sha"))" >/dev/null 2>&1 || true
  elif [ -f "$r/code.pending" ]; then
    mv "$r/out.pending" "$r/out"; mv "$r/code.pending" "$r/code.tmp"
  else
    continue
  fi
  mv "$r/code.tmp" "$r/code"
done

if [ -n "$mirror" ] && [ "$landed" != none ]; then
  if git -C "$root" push -q "$remote" "$landed:refs/heads/$mirror"; then
    echo "mirrored to $mirror" >&2
  else
    echo "mirror to $mirror refused (not a fast-forward?); main is landed, mirror by hand" >&2
  fi
fi

finish_own
