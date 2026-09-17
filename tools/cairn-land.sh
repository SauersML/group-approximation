#!/usr/bin/env bash
# Serialized, batching lander: put verified results on main without touching
# anyone's working tree.
#
#   tools/cairn-land.sh -m SUBJECT [-F BODY_FILE] [--mirror BRANCH] [--node ID] SRC PATH...
#
# SRC is the worktree the result lives in; each PATH is relative to it. The
# request is spooled, then the lander takes a lock shared by every worktree in
# the container. Whoever holds the lock lands every pending request (up to
# CAIRN_LAND_BATCH, default 16): it builds a temporary worktree at origin/main,
# copies all their paths in, regenerates the frontier with `bin/cairn check`
# once (exit 0 required), and makes one commit per request. If the batch fails
# the check, each request is re-checked alone and only the failing ones get
# exit 4. One push lands the batch. A rejected push is never rebased: the
# lander resets to the new origin/main and rebuilds, so the generated
# research/FRONTIER.md never conflicts. It never force-pushes. A waiter whose
# request was landed by another holder prints that holder's result and exits
# with its code.
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
cleanup() { git -C "$root" worktree remove --force "$wt" >/dev/null 2>&1 || true; rm -rf "$wt" "$wt.check.log"; }
trap cleanup EXIT

# Pending requests, oldest first; our own is always included.
batch=()
while IFS= read -r d; do batch+=("$spool/$d"); done < <(
  ls -1 "$spool" | grep -Ev '\.tmp$' | while IFS= read -r d; do
    [ -f "$spool/$d/code" ] || [ ! -f "$spool/$d/msg" ] || printf '%s\n' "$d"
  done | sort | head -n "${CAIRN_LAND_BATCH:-16}")
case " ${batch[*]} " in *" $req "*) ;; *) batch+=("$req") ;; esac
echo "landing a batch of ${#batch[@]} request(s)" >&2

copy_in() {  # copy one request's paths into the worktree
  local r="$1" s p
  s="$(cat "$r/src")"
  while IFS= read -r p; do
    [ -e "$s/$p" ] || { echo "missing in $s: $p" >"$r/out"; return 1; }
    mkdir -p "$wt/$(dirname "$p")"
    if [ -d "$s/$p" ]; then cp -a "$s/$p/." "$wt/$p/"; else cp -a "$s/$p" "$wt/$p"; fi
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

landed="" good=()
for attempt in 1 2 3 4 5 6; do
  git -C "$root" fetch -q "$remote" main
  git -C "$root" worktree remove --force "$wt" >/dev/null 2>&1 || true
  rm -rf "$wt"
  git -C "$root" worktree add -q --detach "$wt" "$remote/main"
  good=()
  for r in "${batch[@]}"; do rm -f "$r/sha" "$r/out.pending" "$r/code.pending"; done

  ok=1
  for r in "${batch[@]}"; do copy_in "$r" || ok=0; done
  if [ "$ok" = 1 ] && check; then
    for r in "${batch[@]}"; do commit_req "$r"; good+=("$r"); done
    if [ -f "$wt/research/FRONTIER.md" ] && [ "$(git -C "$wt" rev-list --count "$remote/main..HEAD")" != 0 ]; then
      git -C "$wt" add research/FRONTIER.md
      git -C "$wt" diff --cached --quiet || git -C "$wt" commit -q --amend --no-edit
    fi
  else
    # Isolate: land each request that passes on its own, report the rest.
    reset_wt
    for r in "${batch[@]}"; do
      if ! copy_in "$r"; then
        echo 4 >"$r/code.pending"; mv "$r/out" "$r/out.pending"; reset_wt; continue
      fi
      if check; then
        [ -f "$wt/research/FRONTIER.md" ] && git -C "$wt" add research/FRONTIER.md
        commit_req "$r"; good+=("$r")
      else
        { echo "bin/cairn check failed on origin/main + these paths; nothing pushed"; tail -40 "$wt.check.log"; } >"$r/out.pending"
        echo 4 >"$r/code.pending"
        reset_wt
      fi
    done
  fi

  # The amend above moves the last commit; recompute every sha from the log.
  n=0; for r in "${good[@]}"; do [ -f "$r/sha" ] && n=$((n + 1)); done
  if [ "$n" = 0 ]; then landed="none"; break; fi
  shas=(); while IFS= read -r s; do shas+=("$s"); done < <(git -C "$wt" rev-list --reverse "$remote/main..HEAD")
  i=0; for r in "${good[@]}"; do [ -f "$r/sha" ] && { printf '%s\n' "${shas[$i]}" >"$r/sha"; i=$((i + 1)); }; done
  if git -C "$wt" push -q "$remote" HEAD:main; then
    landed="$(git -C "$wt" rev-parse HEAD)"
    break
  fi
  echo "push rejected (attempt $attempt); rebuilding on the new $remote/main" >&2
  sleep $((attempt * 2))
done

if [ -z "$landed" ]; then
  echo "could not land after 6 attempts" >&2
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
