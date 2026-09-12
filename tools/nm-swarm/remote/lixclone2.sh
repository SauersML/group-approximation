#!/usr/bin/env bash
# lixclone2.sh <src-clone> <new-clone...>   (runs ON MSI acn112, detached) -- FAST warm clones.
# Hard links (--link-dest) for .lake/packages and .lake/build (lake unlinks before writing, so the source
# clone is never touched; purge_stale.py protects the new clone).  Sources: ONLY what probes read
# (GroupApproximation/, GroupApproximation.lean, lakefile.toml, lake-manifest.json, lean-toolchain, Palomar/)
# -- the job's delta sync only ever touches GroupApproximation + GroupApproximation.lean.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; CC=$P/cc_clones; SRC=$CC/$1; shift
mk_one() {
  local c=$1 D=$CC/$1
  mkdir -p "$D/.nm" "$D/.lake/build"
  touch "$D/.nm/PREP_PENDING"
  exec 9>"$D/.lake/laneprobe.lock"; flock -w 600 9 || { echo "[lixclone2] $c lock timeout"; return; }
  rsync -a --link-dest="$SRC/.lake/packages/" "$SRC/.lake/packages/" "$D/.lake/packages/"
  rsync -a --delete "$SRC/GroupApproximation/" "$D/GroupApproximation/"
  for f in GroupApproximation.lean lakefile.toml lake-manifest.json lean-toolchain; do cp -a "$SRC/$f" "$D/$f"; done
  [ -d "$SRC/Palomar" ] && rsync -a "$SRC/Palomar/" "$D/Palomar/"
  rsync -a --exclude '/build' --exclude '/packages' --exclude '/laneprobe.lock' "$SRC/.lake/" "$D/.lake/"
  rsync -a --delete --link-dest="$SRC/.lake/build/" "$SRC/.lake/build/" "$D/.lake/build/"
  cp -a "$SRC/.nm/base" "$D/.nm/base"; cp -a "$SRC/.nm/lastov" "$D/.nm/lastov" 2>/dev/null || : > "$D/.nm/lastov"
  rm -f "$D/.nm/PREP_PENDING"
  echo "[lixclone2] $c ready $(date +%T) from $(basename $SRC): $(find "$D/.lake/build/lib/lean/GroupApproximation" -name '*.olean' | wc -l) oleans, base $(cut -c1-9 "$D/.nm/base")"
}
export -f mk_one; export CC SRC P
echo "[lixclone2] start $(date) src=$SRC clones: $*"
printf '%s\n' "$@" | xargs -P 8 -I{} bash -c 'mk_one {}'
echo "[lixclone2] done $(date)"
