#!/usr/bin/env bash
# lixclone.sh <src-clone> <new-clone...>   (runs ON MSI, detached)
# Warm LIX clones from the only clone with the CharClass closure built (cs-endpoint).
# Packages AND GroupApproximation artifacts by hard links (--link-dest): lake unlinks an artifact
# before writing its replacement, so the source clone's inodes are never touched; purge_stale.py
# (olean older than source => unlink + dependents) protects the new clone from replaying stale pairs.
# Sources by real copy (mtimes preserved, so the olean/source order carries over).  .nm/base and
# .nm/lastov are copied so the first probe's delta sync restores the source clone's overlay paths.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; CC=$P/cc_clones; SRC=$CC/$1; shift
mk_one() {
  local c=$1 D=$CC/$1
  if [ -e "$D/.nm/base" ] && [ ! -e "$D/.nm/PREP_PENDING" ]; then echo "[lixclone] $c already ready"; return; fi
  mkdir -p "$D/.nm" "$D/.lake/build"
  touch "$D/.nm/PREP_PENDING"
  exec 9>"$D/.lake/laneprobe.lock"; flock -w 600 9 || { echo "[lixclone] $c lock timeout"; return; }
  rsync -a --link-dest="$SRC/.lake/packages/" "$SRC/.lake/packages/" "$D/.lake/packages/"
  rsync -a --exclude '/.lake' --exclude '/.nm' --exclude '*.log' "$SRC/" "$D/"
  rsync -a --exclude '/build' --exclude '/packages' --exclude '/laneprobe.lock' "$SRC/.lake/" "$D/.lake/"
  rsync -a --link-dest="$SRC/.lake/build/" "$SRC/.lake/build/" "$D/.lake/build/"
  cp -a "$SRC/.nm/base" "$D/.nm/base"; cp -a "$SRC/.nm/lastov" "$D/.nm/lastov" 2>/dev/null || touch "$D/.nm/lastov"
  rm -f "$D/.nm/PREP_PENDING"
  echo "[lixclone] $c ready $(date +%T): $(find "$D/.lake/build/lib/lean/GroupApproximation/CharClass" -name '*.olean' | wc -l) CharClass oleans, base $(cut -c1-9 "$D/.nm/base")"
}
export -f mk_one; export CC SRC P
echo "[lixclone] start $(date) src=$SRC clones: $*"
printf '%s\n' "$@" | xargs -P 6 -I{} bash -c 'mk_one {}'
echo "[lixclone] done $(date)"
