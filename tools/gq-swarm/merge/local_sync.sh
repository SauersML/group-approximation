#!/bin/bash
# Fast-forward the shared checkout to origin/main without losing anything on disk:
#   write a tip file only where the disk is absent or holds the old HEAD blob; remove a file main deleted only when the
#   disk holds the old HEAD blob; point .git/index and refs/heads/main at the tip; then, for each dirty path whose
#   exact disk content is saved on main under wip/sync-*/disk/, restore main's copy (tracked) or remove it (untracked).
#   Every other local edit stays.  DO=1 applies; otherwise it prints the plan.
set -uo pipefail
REPO=/Users/user/nonsofic_existence
S=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/merge
DO=${DO:-0}
cd "$REPO" || exit 1
die() { unset GIT_INDEX_FILE; echo "ABORT: $*" >&2; exit 1; }
avail_kb=$(df -k /System/Volumes/Data | awk 'NR==2{print $4}')
[ "$avail_kb" -gt 1048576 ] || die "disk below 1 GiB free"
[ -f .git/MERGE_HEAD ] && die "a merge is in progress in the shared checkout"
[ "$(git symbolic-ref HEAD)" = refs/heads/main ] || die "HEAD is not refs/heads/main"
git fetch -q origin +refs/heads/main:refs/remotes/origin/main || die "fetch"
OLD=$(git rev-parse HEAD); NEW=$(git rev-parse refs/remotes/origin/main)
git merge-base --is-ancestor "$OLD" "$NEW" || die "local main has commits that are not on origin/main"
git diff --cached --no-renames --name-only "$OLD" > "$S/staged.txt"
[ -s "$S/staged.txt" ] && die "the shared index holds staged changes against HEAD; measure them before healing"
echo "OLD $OLD  NEW $NEW  ($(git rev-list --count "$OLD..$NEW") commits)"

# Plan A: tree delta OLD -> NEW.
git diff --no-renames --name-status "$OLD" "$NEW" > "$S/sync.status"
: > "$S/write.txt"; : > "$S/remove.txt"; : > "$S/skip.txt"
while IFS=$'\t' read -r st p; do
  newb=$(git rev-parse -q --verify "${NEW}:$p"); oldb=$(git rev-parse -q --verify "${OLD}:$p")
  if [ -L "$p" ]; then echo "symlink	$p" >> "$S/skip.txt"; continue; fi
  if [ -f "$p" ]; then d=$(git hash-object "$p"); elif [ -e "$p" ]; then echo "not-a-file	$p" >> "$S/skip.txt"; continue; else d=""; fi
  case "$st" in
    A) if [ -z "$d" ]; then echo "$p" >> "$S/write.txt"; elif [ "$d" != "$newb" ]; then echo "added-but-disk-differs	$p" >> "$S/skip.txt"; fi ;;
    M|T) if [ "$d" = "$newb" ]; then :; elif [ -z "$d" ] || [ "$d" = "$oldb" ]; then echo "$p" >> "$S/write.txt"; else echo "local-edit	$p" >> "$S/skip.txt"; fi ;;
    D) if [ -z "$d" ]; then :; elif [ "$d" = "$oldb" ]; then echo "$p" >> "$S/remove.txt"; else echo "deleted-on-main-local-edit	$p" >> "$S/skip.txt"; fi ;;
    *) echo "status-$st	$p" >> "$S/skip.txt" ;;
  esac
done < "$S/sync.status"

# Plan B: dirty paths already saved byte for byte on main under wip/sync-*/disk/.
git status --porcelain=v1 -uall > "$S/dirty.before"
: > "$S/harm.restore"; : > "$S/harm.remove"; : > "$S/harm.keep"
while IFS= read -r l; do
  f="${l:3}"
  [ -f "$f" ] || { echo "$l" >> "$S/harm.keep"; continue; }
  d=$(git hash-object "$f"); saved=""
  for w in wip/sync-2026-09-14/disk wip/sync-2026-09-17/disk; do
    [ "$(git rev-parse -q --verify "${NEW}:$w/$f")" = "$d" ] && saved=$w
  done
  if [ -z "$saved" ]; then echo "$l" >> "$S/harm.keep"
  elif git cat-file -e "${NEW}:$f" 2>/dev/null; then echo "$f" >> "$S/harm.restore"
  else echo "$f" >> "$S/harm.remove"; fi
done < "$S/dirty.before"

echo "plan A: write $(wc -l < "$S/write.txt")  remove $(wc -l < "$S/remove.txt")  keep-local $(wc -l < "$S/skip.txt")"
head -20 "$S/skip.txt"
echo "plan B: restore main copy $(wc -l < "$S/harm.restore")  remove saved untracked $(wc -l < "$S/harm.remove")  keep $(wc -l < "$S/harm.keep")"
cat "$S/harm.keep"
[ "$DO" = 1 ] || { echo "DRY RUN"; exit 0; }

# 1. Write tip files from a private index, so the shared index moves only after the disk is done.
export GIT_INDEX_FILE="$S/sync.index"; rm -f "$GIT_INDEX_FILE"
git read-tree "$NEW" || die "read-tree into private index"
[ "$(git ls-files | wc -l | tr -d ' ')" = "$(git ls-tree -r "$NEW" | wc -l | tr -d ' ')" ] || die "private index count mismatch"
if [ -s "$S/write.txt" ]; then git checkout-index -f --stdin < "$S/write.txt" || die "checkout-index (plan A)"; fi
unset GIT_INDEX_FILE
while IFS= read -r p; do rm -f -- "$p"; done < "$S/remove.txt"

# 2. Shared index and branch pointer.
cp .git/index "$S/shared-index.before"
git read-tree "$NEW" || die "read-tree into the shared index"
[ "$(git ls-files | wc -l | tr -d ' ')" = "$(git ls-tree -r "$NEW" | wc -l | tr -d ' ')" ] || die "shared index count mismatch"
git update-ref refs/heads/main "$NEW" "$OLD" || die "update-ref refused (main moved under us)"

# 3. Plan B.
if [ -s "$S/harm.restore" ]; then git checkout-index -f --stdin < "$S/harm.restore" || die "checkout-index (plan B)"; fi
while IFS= read -r f; do rm -f -- "$f"; rmdir -p "$(dirname "$f")" 2>/dev/null || true; done < "$S/harm.remove"

git update-index -q --refresh > /dev/null
echo "=== after ==="
git rev-parse --short HEAD
git diff --cached --no-renames --name-only HEAD | wc -l | xargs echo "staged vs HEAD:"
git status --porcelain=v1 -uall | cut -c1-2 | sort | uniq -c
git status --porcelain=v1 -uall | head -20
