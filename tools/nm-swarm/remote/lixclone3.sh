#!/usr/bin/env bash
# lixclone3.sh <src> <clone...> (acn112, detached): packages by SYMLINK to the source clone (probes never write
# packages; hard-linking ~10^5 package files took >25 min on vast), GroupApproximation build by --link-dest.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; CC=$P/cc_clones; SRC=$CC/$1; shift
for c in "$@"; do pkill -u __MSI_USER__ -f "mk_one $c\$"; pkill -u __MSI_USER__ -f "cc_clones/$c/"; done
sleep 3
one() {
  local c=$1 D=$CC/$1
  mkdir -p "$D/.nm" "$D/.lake/build"; touch "$D/.nm/PREP_PENDING"
  exec 9>"$D/.lake/laneprobe.lock"; flock -w 120 9 || { echo "[lixclone3] $c lock timeout"; return; }
  if [ ! -L "$D/.lake/packages" ]; then [ -e "$D/.lake/packages" ] && mv "$D/.lake/packages" "$D/.lake/packages.partial-$(date +%s)"; ln -s "$SRC/.lake/packages" "$D/.lake/packages"; fi
  rsync -a --delete "$SRC/GroupApproximation/" "$D/GroupApproximation/"
  for f in GroupApproximation.lean lakefile.toml lake-manifest.json lean-toolchain; do cp -a "$SRC/$f" "$D/$f"; done
  [ -d "$SRC/Palomar" ] && rsync -a "$SRC/Palomar/" "$D/Palomar/"
  rsync -a --exclude '/build' --exclude '/packages' --exclude '/packages.partial-*' --exclude '/laneprobe.lock' "$SRC/.lake/" "$D/.lake/"
  rsync -a --delete --link-dest="$SRC/.lake/build/" "$SRC/.lake/build/" "$D/.lake/build/"
  cp -a "$SRC/.nm/base" "$D/.nm/base"; cp -a "$SRC/.nm/lastov" "$D/.nm/lastov" 2>/dev/null || : > "$D/.nm/lastov"
  rm -f "$D/.nm/PREP_PENDING"
  echo "[lixclone3] $c ready $(date +%T): $(find "$D/.lake/build/lib/lean/GroupApproximation" -name '*.olean' | wc -l) oleans, base $(cut -c1-9 "$D/.nm/base")"
}
echo "[lixclone3] start $(date)"
for c in "$@"; do one "$c" & done; wait
echo "[lixclone3] done $(date)"
