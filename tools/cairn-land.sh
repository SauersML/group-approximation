#!/usr/bin/env bash
# Serialized lander: put one verified result on main without touching anyone's
# working tree.
#
#   tools/cairn-land.sh -m SUBJECT [-F BODY_FILE] [--mirror BRANCH] [--node ID] SRC PATH...
#
# SRC is the worktree the result lives in; each PATH is relative to it. The
# lander takes a lock shared by every worktree in the container, builds a
# temporary worktree at origin/main, copies the paths in, regenerates the
# frontier with `bin/cairn check` (exit 0 required), commits, and pushes to
# main. A rejected push is never rebased: the lander resets to the new
# origin/main, copies again, re-checks and recommits, so the generated
# research/FRONTIER.md never conflicts. It never force-pushes.
#
# Trailers come from $CAIRN_LAND_TRAILERS (a file whose lines are appended to
# the message). --mirror pushes the same commit to BRANCH only as a
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
[ -n "$subject" ] && [ $# -ge 2 ] || { sed -n '2,20p' "$0" >&2; exit 64; }
src="$(cd "$1" && pwd)"; shift
paths=("$@")

root="$(cd "$(dirname "$0")/.." && pwd)"
for p in "${paths[@]}"; do
  case "$p" in /*|*..*) echo "path must be relative and inside SRC: $p" >&2; exit 64 ;; esac
  [ -e "$src/$p" ] || { echo "missing in $src: $p" >&2; exit 4; }
done

state="${CAIRN_LIVE:-$(CAIRN_ROOT="$root" python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); import cairn, os; print(os.path.join(cairn.shared_dir(), "live"))' "$root/tools")}"
mkdir -p "$state"
exec 9>"$state/land.lock"
echo "waiting for the land lock ($state/land.lock)" >&2
flock 9

msg="$(mktemp)"; wt="$(mktemp -d)"
cleanup() { git -C "$root" worktree remove --force "$wt" >/dev/null 2>&1 || true; rm -rf "$wt" "$msg"; }
trap cleanup EXIT
{
  printf '%s\n' "$subject"
  if [ -n "$body_file" ]; then printf '\n'; cat "$body_file"; fi
  if [ -n "${CAIRN_LAND_TRAILERS:-}" ]; then printf '\n'; cat "$CAIRN_LAND_TRAILERS"; fi
} >"$msg"

landed=""
for attempt in 1 2 3 4 5 6; do
  git -C "$root" fetch -q "$remote" main
  git -C "$root" worktree remove --force "$wt" >/dev/null 2>&1 || true
  rm -rf "$wt"
  git -C "$root" worktree add -q --detach "$wt" "$remote/main"
  for p in "${paths[@]}"; do
    mkdir -p "$wt/$(dirname "$p")"
    if [ -d "$src/$p" ]; then cp -a "$src/$p/." "$wt/$p/"; else cp -a "$src/$p" "$wt/$p"; fi
  done
  if ! (cd "$wt" && bin/cairn check >"$wt.check.log" 2>&1); then
    echo "bin/cairn check failed on origin/main + these paths; nothing pushed" >&2
    tail -40 "$wt.check.log" >&2; rm -f "$wt.check.log"
    exit 4
  fi
  rm -f "$wt.check.log"
  git -C "$wt" add -- "${paths[@]}"
  [ -f "$wt/research/FRONTIER.md" ] && git -C "$wt" add research/FRONTIER.md
  if git -C "$wt" diff --cached --quiet; then
    echo "nothing to land: origin/main already has these paths" >&2
    exit 0
  fi
  git -C "$wt" commit -q -F "$msg"
  if git -C "$wt" push -q "$remote" HEAD:main; then
    landed="$(git -C "$wt" rev-parse HEAD)"
    break
  fi
  echo "push rejected (attempt $attempt); rebuilding on the new $remote/main" >&2
  sleep $((attempt * 2))
done
[ -n "$landed" ] || { echo "could not land after 6 attempts" >&2; exit 1; }
echo "landed $landed on $remote/main"

if [ -n "$mirror" ]; then
  if git -C "$root" push -q "$remote" "$landed:refs/heads/$mirror"; then
    echo "mirrored to $mirror"
  else
    echo "mirror to $mirror refused (not a fast-forward?); main is landed, mirror by hand" >&2
  fi
fi

CAIRN_ROOT="$root" CAIRN_LIVE="$state" CAIRN_AGENT="${CAIRN_AGENT:-lander}" \
  python3 "$root/tools/cairn_live.py" landed ${node:+--node "$node"} \
  --text "$subject ($landed)" >/dev/null || true
