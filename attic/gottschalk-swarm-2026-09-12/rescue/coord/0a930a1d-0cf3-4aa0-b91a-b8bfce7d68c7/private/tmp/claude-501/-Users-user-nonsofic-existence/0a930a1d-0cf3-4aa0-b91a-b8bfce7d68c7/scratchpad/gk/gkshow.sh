#!/bin/bash
# gkshow.sh <repo-path> [<outfile>]
# Print main's live tip and the path's blob there; copy main's content to <outfile> if given.
# Use the printed blob in GK_ACK="<repo-path>=<blob>" after merging your edit into that copy.
set -u
R=/Users/user/nonsofic_existence
cd "$R" || exit 1
P="${1:?repo path}"
T=$(git ls-remote origin refs/heads/main | cut -f1)
[ -n "$T" ] || { echo "ls-remote failed"; exit 1; }
git cat-file -e "${T}^{commit}" 2>/dev/null || git fetch -q origin "$T" 2>/dev/null || git fetch -q origin main
git cat-file -e "${T}^{commit}" 2>/dev/null || { echo "cannot fetch ${T}"; exit 1; }
if git cat-file -e "${T}:${P}" 2>/dev/null; then
  b=$(git rev-parse "${T}:${P}")
  echo "tip=${T} blob=${b} path=${P}"
  if [ -n "${2:-}" ]; then git show "${T}:${P}" > "$2" && echo "wrote $2"; fi
else
  echo "tip=${T} ABSENT ${P}"
fi
