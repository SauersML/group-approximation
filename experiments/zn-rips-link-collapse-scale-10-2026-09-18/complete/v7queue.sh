#!/bin/bash
# ./v7queue.sh : worker; takes the next "X i" job from v7jobs.txt (under flock) and replays stage X_i with kzv7
# via vpiece7.sh from ord/sX_{i-1} (O order); results go to v7done.txt / v7fail.txt
cd "$(dirname "$0")" || exit 1
while true; do
  job=$(flock v7jobs.lock bash -c 'j=$(head -n 1 v7jobs.txt); [ -n "$j" ] && tail -n +2 v7jobs.txt > v7jobs.t && mv v7jobs.t v7jobs.txt; echo "$j"')
  [ -z "$job" ] && exit 0; set -- $job; X=$1; i=$2
  flock ord.lock ./mkord.sh $X $((i-1)) || { echo "$job mkord" >> v7fail.txt; continue; }
  if (cd .. && ./vpiece7.sh ${X}$i sg/ord/s${X}_$((i-1)).txt sg/k${X}_$i.txt sg/s${X}_$i.txt); then echo "$(date -u +%H:%M:%S) $job" >> v7done.txt
  else echo "$(date -u +%H:%M:%S) $job" >> v7fail.txt; fi
done
