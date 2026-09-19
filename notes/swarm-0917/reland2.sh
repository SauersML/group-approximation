#!/bin/bash
S=/tmp/claude-0/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/scratchpad
ENV="CAIRN_LAND_TRAILERS=$S/trailers.txt CAIRN_WAVE=swarm-0917 CAIRN_LIVE_SYNC=origin CAIRN_LIVE_REF=refs/heads/cairn-live-bus-0917"
awk -F'\t' '$4=="unlanded" && $5!="-"' $S/${STATE:-w7-state.tsv} | while IFS=$'\t' read K ID ST L W; do
  echo "=== $K $ID $W"
  cd "$W" || continue
  git checkout -- research/FRONTIER.md 2>/dev/null
  git rm -q --cached -r --ignore-unmatch '*__pycache__*' >/dev/null 2>&1; find . -name __pycache__ -prune -exec rm -rf {} + 2>/dev/null
  [ -n "$(git status --porcelain)" ] && { git add -A; git reset -q research/FRONTIER.md 2>/dev/null; git checkout -- research/FRONTIER.md 2>/dev/null; git commit -qm "local: $K"; }
  for i in 1 2 3; do git fetch -q origin main && break; sleep 3; done
  git merge -q --no-edit origin/main || { echo mergefail; git merge --abort; continue; }
  FILES=$(git diff --name-only origin/main HEAD | grep -v '^research/FRONTIER.md$')
  echo "files: $FILES" | tr '\n' ' '; echo
  [ -z "$FILES" ] && { echo "nothing to land"; continue; }
  bin/cairn check > $S/check-$K.txt 2>&1; c=$?; echo check $c; git checkout -- research/FRONTIER.md 2>/dev/null
  [ $c = 0 ] || { grep -i error $S/check-$K.txt | head -8; continue; }
  env $ENV CAIRN_AGENT=$K tools/cairn-land.sh -m "$K: $ID" --node $ID "$PWD" $FILES 2>&1 | tail -2; echo exit ${PIPESTATUS[0]}
done
echo ALLDONE
