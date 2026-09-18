#!/bin/bash
# usage: hold.sh TODO.tsv HOLD.tsv   (TODO rows: key id landed worktree)
# Saves each finished lane's worktree HEAD to refs/swarm-hold/<key>, removes the worktree,
# then merges the held shas into the current branch.
S=/tmp/claude-0/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/scratchpad
R=/home/user/group-approximation
TODO=$1; HOLD=$2
cd $R || exit 1
while IFS=$'\t' read -r k id landed w; do
  [ -d "$w" ] || { echo "missing worktree $k $w"; continue; }
  if [ -n "$(git -C $w status --porcelain)" ]; then
    git -C $w add -A && git -C $w -c user.name=swarm -c user.email=noreply@anthropic.com commit -qm "swarm lane $k: uncommitted work" -m "$(cat $S/trailers.txt)"
  fi
  sha=$(git -C $w rev-parse HEAD)
  git update-ref refs/swarm-hold/$k $sha
  git worktree remove -f -f $w
  printf '%s\t%s\t%s\t%s\n' "$k" "$id" "$landed" "$sha" >> $HOLD
  echo "held $k $sha"
done < $TODO
git worktree prune
while IFS=$'\t' read -r k id landed w; do
  sha=$(git rev-parse -q --verify refs/swarm-hold/$k) || continue
  git merge-base --is-ancestor $sha HEAD && continue
  if ! git merge -q --no-edit -m "Merge swarm lane $k" -m "$(cat $S/trailers.txt)" $sha 2>/dev/null; then
    for f in $(git diff --name-only --diff-filter=U); do
      case "$f" in
        research/FRONTIER.md) git checkout --theirs -- "$f" ;;
        *.md|*.txt|*.py|*.json) python3 $S/union.py "$f" ;;
        *) git checkout --theirs -- "$f" ;;
      esac
      git add -- "$f"
    done
    if git grep -lE '^(<<<<<<<|>>>>>>>) ' -- $(git diff --cached --name-only) >/dev/null 2>&1; then
      echo "markers remain for $k; aborting"; git merge --abort; continue
    fi
    git commit -q --no-edit || { echo "commit failed $k"; git merge --abort; continue; }
  fi
  echo "merged $k"
done < $TODO
