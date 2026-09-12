#!/usr/bin/env bash
# prep.sh <SHA> <clone> [<clone> ...]        (runs ON MSI, detached; log $NMR/prep-<tag>.log)
#
# 1. Mark every lane clone PREP_PENDING (probes defer, exit 5).
# 2. Base warm build: lead clone := origin/main@SHA, root build through SLURM (32 cpus).
# 3. Copy the lead clone's sources (times preserved) and GroupApproximation build
#    artifacts (REAL copies, never hard links) into each lane clone under that clone's
#    probe lock; create missing clones by copying the lead clone whole.  Clear the marker.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; NMR=$P/nm; CC=$P/cc_clones; LEAD=$CC/lead
SHA=$1; shift; CLONES="$*"
TAG=$(date +%m%d-%H%M%S)
echo "[prep] start $(date) sha=$SHA clones: $CLONES"
for c in $CLONES; do mkdir -p "$CC/$c/.nm" "$CC/$c/.lake"; touch "$CC/$c/.nm/PREP_PENDING"; done
mkdir -p "$LEAD/.nm"
sed -e "s|__CLONE__|$LEAD|" -e "s|__TAG__|base-$TAG|" -e "s|__SHA__|$SHA|" -e "s|__MODS__||" -e "s|__TARGETS__||" "$NMR/wirejob.template.sh" > "$LEAD/.nm/basejob-$TAG.sh"
mkdir -p "$LEAD/.nm"
SLURM_TIME=${PREP_TIME:-05:00:00} bash "$NMR/dispatch.sh" "$LEAD/.nm/basejob-$TAG.sh" "$LEAD/.nm/baseout-$TAG.txt" nm-base "${PREP_CPUS:-64}"
echo "[prep] base build finished rc=$? $(date)"
du -sh "$LEAD/.lake/build/lib/lean/GroupApproximation" "$LEAD/.lake/build/ir/GroupApproximation" 2>/dev/null
copy_one() {
  local c=$1 D=$CC/$1
  exec 9>"$D/.lake/laneprobe.lock"; flock -w 7200 9 || { echo "[prep] $c lock timeout"; return; }
  if [ ! -d "$D/.lake/packages/mathlib" ]; then
    echo "[prep] $c: creating whole copy of lead"
    rsync -a --exclude '/.lake/build' --exclude '/.nm' --exclude '*.log' "$LEAD/" "$D/"
  fi
  rsync -a --delete "$LEAD/GroupApproximation/" "$D/GroupApproximation/"
  cp -a "$LEAD/GroupApproximation.lean" "$D/GroupApproximation.lean"
  for sub in lib/lean ir; do
    mkdir -p "$D/.lake/build/$sub"
    rm -rf "$D/.lake/build/$sub/GroupApproximation" "$D/.lake/build/$sub/GroupApproximation."*
    cp -a "$LEAD/.lake/build/$sub/GroupApproximation" "$D/.lake/build/$sub/" 2>/dev/null
    cp -a "$LEAD/.lake/build/$sub/GroupApproximation."* "$D/.lake/build/$sub/" 2>/dev/null
  done
  rm -f "$D/.nm/PREP_PENDING"
  echo "[prep] $c ready $(date +%T): $(find "$D/.lake/build/lib/lean/GroupApproximation" -name '*.olean' | wc -l) oleans"
}
n=0
for c in $CLONES; do
  copy_one "$c" &
  n=$((n+1)); if [ $((n % 4)) -eq 0 ]; then wait; fi
done
wait
echo "[prep] done $(date)"
