#!/bin/bash
S=/tmp/claude-0/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/scratchpad
J=/root/.claude/projects/-home-user-group-approximation/6559a301-b52c-57ef-bef5-35eb6d3deb43/subagents/workflows/$1/journal.jsonl
H=$S/$2
cd /home/user/group-approximation
for i in $(seq 1 60); do
  python3 $S/todo.py $J $H > $S/auto-todo.tsv 2>>$S/autohold.log
  if [ -s $S/auto-todo.tsv ]; then
    for w in $(cut -f4 $S/auto-todo.tsv); do git worktree unlock $w 2>/dev/null; done
    bash $S/hold.sh $S/auto-todo.tsv $H 2>&1 | grep -E '^(held|merged|markers|commit|missing)' >> $S/autohold.log
  fi
  echo "$(date -u +%H:%M) $(df -h --output=avail / | tail -1) held=$(wc -l < $H)" >> $S/autohold.log
  sleep 180
done
