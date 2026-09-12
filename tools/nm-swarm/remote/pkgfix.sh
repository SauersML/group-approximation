#!/usr/bin/env bash
# pkgfix.sh  -- nm-a..nm-d: stop their slow whole-copy workers; Mathlib/package tree by hard links
# (--link-dest; probes never write packages), sources and small .lake files by rsync, GroupApproximation
# artifacts by REAL copies (CharClass excluded); clear the marker.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; CC=$P/cc_clones; LEAD=$CC/lead
for c in nm-a nm-b nm-c nm-d; do pkill -u __MSI_USER__ -f "[c]opy_one $c"; done
pkill -u __MSI_USER__ -f "[r]sync -a --exclude /.lake/build --exclude /.nm --exclude"
sleep 5
fix_one() {
  local c=$1 D=$CC/$1
  mkdir -p "$D/.nm" "$D/.lake"
  exec 9>"$D/.lake/laneprobe.lock"; flock -w 900 9 || { echo "[pkgfix] $c lock timeout"; return; }
  rsync -a --link-dest="$LEAD/.lake/packages/" "$LEAD/.lake/packages/" "$D/.lake/packages/"
  rsync -a --exclude '/.lake/build' --exclude '/.lake/packages' --exclude '/.nm' --exclude '*.log' "$LEAD/" "$D/"
  for sub in lib/lean ir; do
    mkdir -p "$D/.lake/build/$sub/GroupApproximation"
    rsync -a --delete --exclude '/CharClass/' "$LEAD/.lake/build/$sub/GroupApproximation/" "$D/.lake/build/$sub/GroupApproximation/"
  done
  rm -f "$D/.nm/PREP_PENDING"
  echo "[pkgfix] $c ready $(date +%T): $(find "$D/.lake/build/lib/lean/GroupApproximation" -name '*.olean' | wc -l) oleans"
}
export -f fix_one; export CC LEAD P
echo "[pkgfix] start $(date)"
printf '%s\n' nm-a nm-b nm-c nm-d | xargs -P 4 -I{} bash -c 'fix_one {}'
echo "[pkgfix] done $(date)"
