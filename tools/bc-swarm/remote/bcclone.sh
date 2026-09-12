#!/usr/bin/env bash
# bcclone.sh <src-clone-name>   (runs ON MSI, detached)
# Create or reset the ONE Bowen–Chapman campaign clone $P/bc_clones/bc from a warm non-MF swarm clone:
# packages by SYMLINK to the stable package tree the LIX clones already share (probes never write packages;
# bcjob.template.sh refuses to build if lake-manifest.json drifts), GroupApproximation build by --link-dest from the
# source clone, and SOURCES exported from the MSI mirror at the source clone's base commit, never copied from the
# source clone's working tree (which may carry lane overlays or a half-synced state).
# Guards (09-12 wipe): the base commit must be in the mirror and carry GroupApproximation.lean, lake-manifest.json and
# lakefile.toml; every git, tar and rsync step must exit 0; a clone path is deleted only when the base tree lacks it
# (checked twice); the clone's source paths must equal the base tree exactly before PREP_PENDING is cleared.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__
SRC=$P/cc_clones/${1:?usage: bcclone.sh <src-clone-name>}
PKGROOT=$P/cc_clones/cs-endpoint; PKG=$PKGROOT/.lake/packages
D=$P/bc_clones/bc; MIR=$P/nm/mirror.git
SYNC_PATHS="GroupApproximation GroupApproximation.lean Palomar lakefile.toml lake-manifest.json lean-toolchain"
csort() { LC_ALL=C sort "$@"; }
ccomm() { LC_ALL=C comm "$@"; }
fail() { echo "[bcclone] REFUSED: $1 (clone left PREP_PENDING)"; exit 4; }
listdisk() { ( cd "$D" && for s in $SYNC_PATHS; do
    if [ -d "$s" ]; then find "$s" \( -type f -o -type l \); elif [ -e "$s" ]; then echo "$s"; fi
  done ) | csort; }
SB=$(cat "$SRC/.nm/base" 2>/dev/null)
echo "[bcclone] start $(date +%T) src=$1 base=${SB:0:9}"
mkdir -p "$D/.nm" "$D/.lake/build"; touch "$D/.nm/PREP_PENDING"
exec 9>"$D/.lake/laneprobe.lock"; flock -w 120 9 || fail "clone lock timeout"
git -C "$MIR" cat-file -e "$SB^{commit}" 2>/dev/null || fail "source clone base '$SB' not in the mirror"
for root in GroupApproximation.lean lake-manifest.json lakefile.toml; do
  git -C "$MIR" cat-file -e "$SB:$root" 2>/dev/null || fail "base ${SB:0:9} lacks $root (gutted tree)"
done
git -C "$MIR" ls-tree -r --name-only "$SB" -- $SYNC_PATHS > "$D/.nm/clonetree.raw" || fail "ls-tree of ${SB:0:9}"
csort "$D/.nm/clonetree.raw" > "$D/.nm/clonetree"; rm -f "$D/.nm/clonetree.raw"
[ -s "$D/.nm/clonetree" ] || fail "empty tree listing for ${SB:0:9}"
PRESENT=""
for s in $SYNC_PATHS; do git -C "$MIR" cat-file -e "$SB:$s" 2>/dev/null && PRESENT="$PRESENT $s"; done
[ -L "$D/.lake/packages" ] || ln -s "$PKG" "$D/.lake/packages" || fail "package symlink"
git -C "$MIR" archive "$SB" $PRESENT | tar -x -m -C "$D"; st=("${PIPESTATUS[@]}")
[ "${st[0]}" = 0 ] && [ "${st[1]}" = 0 ] || fail "archive/extract of ${SB:0:9} (git ${st[0]}, tar ${st[1]})"
listdisk > "$D/.nm/clonedisk"
ccomm -13 "$D/.nm/clonetree" "$D/.nm/clonedisk" > "$D/.nm/cloneextra"
while IFS= read -r path; do
  [ -n "$path" ] || continue
  if git -C "$MIR" cat-file -e "$SB:$path" 2>/dev/null; then fail "refusing to delete $path, which ${SB:0:9} still has"; fi
  rm -f "$D/$path"
done < "$D/.nm/cloneextra"
listdisk > "$D/.nm/clonedisk"
[ -z "$(ccomm -3 "$D/.nm/clonetree" "$D/.nm/clonedisk" | head -1)" ] || fail "clone sources differ from the tree of ${SB:0:9} after export"
rsync -a --exclude '/build' --exclude '/packages' --exclude '/packages.partial-*' --exclude '/laneprobe.lock' \
  "$SRC/.lake/" "$D/.lake/" || fail "rsync of .lake metadata"
rsync -a --delete --link-dest="$SRC/.lake/build/" "$SRC/.lake/build/" "$D/.lake/build/" || fail "rsync of the build tree"
md5sum < "$PKGROOT/lake-manifest.json" | cut -c1-32 > "$D/.nm/manifest.md5"
[ "$(md5sum < "$D/lake-manifest.json" | cut -c1-32)" = "$(cat "$D/.nm/manifest.md5")" ] \
  || fail "lake-manifest.json at ${SB:0:9} differs from the shared package tree"
echo "$SB" > "$D/.nm/base"
: > "$D/.nm/lastov"
rm -f "$D/.nm/clonetree" "$D/.nm/clonedisk" "$D/.nm/cloneextra"
rm -f "$D/.nm/PREP_PENDING"
echo "[bcclone] ready $(date +%T): $(find "$D/.lake/build/lib/lean/GroupApproximation" -name '*.olean' | wc -l) oleans, $(find "$D/GroupApproximation" -name '*.lean' | wc -l) sources, base $(cut -c1-9 "$D/.nm/base")"
echo BCCLONE_DONE
