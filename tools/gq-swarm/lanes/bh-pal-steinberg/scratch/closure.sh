#!/usr/bin/env bash
# BFS over project imports at a commit, reading files with git show only.  usage: closure.sh <sha> <module>...
cd /Users/user/nonsofic_existence
SHA=$1; shift
seen=$(mktemp); todo=$(mktemp); printf '%s\n' "$@" > "$todo"
while [ -s "$todo" ]; do
  m=$(head -1 "$todo"); sed -i '' 1d "$todo"
  grep -qxF "$m" "$seen" && continue; echo "$m" >> "$seen"
  git show "$SHA:${m//.//}.lean" 2>/dev/null | awk '/^import /{print $2; next} /^(namespace|section|noncomputable|open|\/-!)/{exit}' | grep -E '^(GroupApproximation|Palomar)' | while read -r i; do grep -qxF "$i" "$seen" || echo "$i" >> "$todo"; done
done
sort "$seen"; rm -f "$seen" "$todo"
