#!/usr/bin/env bash
# lockstats.sh [N]   (runs ON MSI, read-only)
# Clone-lock contention for the ONE Bowen–Chapman campaign clone, from the rows bcjob.template.sh appends to
# .nm/lockwait.tsv (tag, lane, job start, lock acquired). For the last N acquisitions (default 20) it prints the
# submit-to-lock wait (probe tag time to lock acquisition, what a lane experiences) and the job-start-to-lock wait,
# each as median and max, plus the jobs still waiting for the lock and their ages. Markers older than the job's
# 4 h lock timeout are reported as stale and not counted.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; CLONE=$P/bc_clones/bc; N=${1:-20}
T=$CLONE/.nm/lockwait.tsv; NOW=$(date +%s); Y=$(date +%Y); W=$P/bc/lockstats.$$
median() { sort -n | awk '{a[NR]=$1} END { if (NR == 0) { print "na"; exit } if (NR % 2) print a[(NR+1)/2]; else print int((a[NR/2] + a[NR/2+1]) / 2) }'; }
if [ -s "$T" ]; then
  tail -n "$N" "$T" > "$W.rows"
  while IFS=$'\t' read -r tag lane t0 tl; do
    ts=""
    case "$tag" in
      [0-9][0-9][0-9][0-9]-[0-9][0-9][0-9][0-9][0-9][0-9]-*)
        ts=$(date -d "$Y-${tag:0:2}-${tag:2:2} ${tag:5:2}:${tag:7:2}:${tag:9:2}" +%s 2>/dev/null) ;;
    esac
    [ -n "$ts" ] && echo "$((tl - ts)) $((tl - t0)) $lane $tag"
  done < "$W.rows" > "$W.waits"
  echo "last $(wc -l < "$W.rows" | tr -d ' ') acquisitions ($(wc -l < "$W.waits" | tr -d ' ') with probe tag times), since $(date -d @"$(head -1 "$W.rows" | cut -f4)" +%T)"
  echo "submit_to_lock median=$(cut -d' ' -f1 "$W.waits" | median)s max=$(cut -d' ' -f1 "$W.waits" | sort -n | tail -1)s"
  echo "jobstart_to_lock median=$(cut -d' ' -f2 "$W.waits" | median)s max=$(cut -d' ' -f2 "$W.waits" | sort -n | tail -1)s"
  echo "slowest in window:"; sort -rn "$W.waits" | head -3 | sed 's/^/  /'
  rm -f "$W.rows" "$W.waits"
else
  echo "last 0 acquisitions (no rows recorded yet)"
fi
nw=0; oldest=0
for f in "$CLONE"/.nm/waiting-*; do
  [ -f "$f" ] || continue
  read -r t0 lane < "$f"; age=$((NOW - t0))
  if [ "$age" -gt 14400 ]; then echo "stale marker ${f##*/} age=${age}s"; continue; fi
  nw=$((nw + 1)); [ "$age" -gt "$oldest" ] && oldest=$age
  echo "waiting ${f##*/waiting-} lane=$lane age=${age}s"
done
echo "current_waiters=$nw oldest_wait=${oldest}s"
