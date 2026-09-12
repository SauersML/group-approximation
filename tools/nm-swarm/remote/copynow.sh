#!/usr/bin/env bash
# copynow.sh <clone...>   (runs ON MSI, detached)
# The base root build's tail is a long serial CharClass chain that the non-MF lanes do not need.
# Stop the prep script (so it never re-copies over lanes' work later), let the SLURM base job keep
# running in the lead clone, and copy the lead clone's sources (times preserved) and every
# GroupApproximation artifact EXCEPT the CharClass subtree (still being written) into each lane
# clone under that clone's probe lock; clear the marker.  A module importing CharClass has its
# stale/missing-import artifacts purged by purge_stale.py at the lane's next probe.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; CC=$P/cc_clones; LEAD=$CC/lead
pkill -u __MSI_USER__ -f "[b]ash prep.sh"
echo "[copynow] start $(date) clones: $*"
copy_one() {
  local c=$1 D=$CC/$1
  mkdir -p "$D/.nm" "$D/.lake"
  exec 9>"$D/.lake/laneprobe.lock"; flock -w 7200 9 || { echo "[copynow] $c lock timeout"; return; }
  if [ ! -d "$D/.lake/packages/mathlib" ]; then
    echo "[copynow] $c: whole copy of lead (no build dir)"
    rsync -a --exclude '/.lake/build' --exclude '/.nm' --exclude '*.log' "$LEAD/" "$D/"
    mkdir -p "$D/.nm"
  fi
  rsync -a --delete "$LEAD/GroupApproximation/" "$D/GroupApproximation/"
  cp -a "$LEAD/GroupApproximation.lean" "$D/GroupApproximation.lean"
  for sub in lib/lean ir; do
    mkdir -p "$D/.lake/build/$sub"
    rm -rf "$D/.lake/build/$sub/GroupApproximation" "$D/.lake/build/$sub/GroupApproximation."*
    rsync -a --exclude '/CharClass/' "$LEAD/.lake/build/$sub/GroupApproximation/" "$D/.lake/build/$sub/GroupApproximation/"
  done
  rm -f "$D/.nm/PREP_PENDING"
  echo "[copynow] $c ready $(date +%T): $(find "$D/.lake/build/lib/lean/GroupApproximation" -name '*.olean' | wc -l) oleans"
}
n=0
for c in "$@"; do
  copy_one "$c" &
  n=$((n+1)); if [ $((n % 4)) -eq 0 ]; then wait; fi
done
wait
echo "[copynow] done $(date)"
