#!/usr/bin/env bash
# gqland-lean-green.sh <lane> <msgfile> <path> [<path> ...]
# The lander for Lean. It is gqland-lean.sh plus one guard: every .lean path must match, byte for byte, a GREEN
# record of THIS lane in $GQ/state/green/<lane>.* (written by gqprobe-lean.sh). If you edit after a green, probe again.
# Non-Lean paths (research/*.md, artifacts, Palomar json, yaml) need no record.
set -uo pipefail
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
LANE=${1:?usage: gqland-lean-green.sh <lane> <msgfile> <path...>}; MSG=${2:?msgfile}; shift 2
[ $# -ge 1 ] || { echo "usage: gqland-lean-green.sh <lane> <msgfile> <path...>"; exit 2; }
for p in "$@"; do
  case "$p" in
    *.lean)
      [ -f "$GQ/work/$LANE/$p" ] || { echo "REFUSED: missing $GQ/work/$LANE/$p"; exit 2; }
      h=$(md5 -q "$GQ/work/$LANE/$p") || exit 2
      ls "$GQ/state/green/$LANE".* >/dev/null 2>&1 || { echo "REFUSED: lane $LANE has no GREEN probe record; run gqprobe-lean.sh first"; exit 2; }
      grep -qxF "$h $p" "$GQ/state/green/$LANE".* || { echo "REFUSED: $p has no GREEN probe record with these bytes; run gqprobe-lean.sh again"; exit 2; }
      if grep -nE '^[^-]*\b(sorry|admit)\b' "$GQ/work/$LANE/$p" | grep -vE '^\s*[0-9]+:\s*(--|/-|\*)' | grep -q .; then
        echo "WARNING: $p mentions sorry/admit outside a line comment; land only if that is inside a docstring"; fi;;
  esac
done
exec bash "$GQ/gqland-lean.sh" "$LANE" "$MSG" "$@"
