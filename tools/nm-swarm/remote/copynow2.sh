#!/usr/bin/env bash
# copynow2.sh <clone...>   (runs ON MSI, detached)  -- faster, resumable clone preparation.
# No rm -rf: rsync -a --delete continues any partial copy (identical size+mtime files are skipped)
# and removes extraneous old artifacts.  CharClass (still being built in the lead clone) is
# excluded.  Real copies only (never hard links).  Up to 10 clones in parallel.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; CC=$P/cc_clones; LEAD=$CC/lead
copy_one() {
  local c=$1 D=$CC/$1
  mkdir -p "$D/.nm" "$D/.lake"
  exec 9>"$D/.lake/laneprobe.lock"; flock -w 7200 9 || { echo "[copynow2] $c lock timeout"; return; }
  if [ ! -d "$D/.lake/packages/mathlib" ]; then
    rsync -a --exclude '/.lake/build' --exclude '/.nm' --exclude '*.log' "$LEAD/" "$D/"; mkdir -p "$D/.nm"
  fi
  rsync -a --delete "$LEAD/GroupApproximation/" "$D/GroupApproximation/"
  cp -a "$LEAD/GroupApproximation.lean" "$D/GroupApproximation.lean"
  for sub in lib/lean ir; do
    mkdir -p "$D/.lake/build/$sub/GroupApproximation"
    rm -f "$D/.lake/build/$sub/GroupApproximation."*
    rsync -a --delete --exclude '/CharClass/' "$LEAD/.lake/build/$sub/GroupApproximation/" "$D/.lake/build/$sub/GroupApproximation/"
  done
  rm -f "$D/.nm/PREP_PENDING"
  echo "[copynow2] $c ready $(date +%T): $(find "$D/.lake/build/lib/lean/GroupApproximation" -name '*.olean' | wc -l) oleans"
}
export -f copy_one; export CC LEAD P
echo "[copynow2] start $(date) clones: $*"
printf '%s\n' "$@" | xargs -P 10 -I{} bash -c 'copy_one {}'
echo "[copynow2] done $(date)"
