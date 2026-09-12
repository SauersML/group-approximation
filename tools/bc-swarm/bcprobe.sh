#!/usr/bin/env bash
# bcprobe.sh <lane> <overlay files...> -- <Module.Name...>
#
# Build the named modules ON MSI in the ONE Bowen–Chapman campaign clone, against
#   origin/main (tip at probe time, from the shared MSI mirror)  +  the overlay files named on the command line
# (repo-relative paths: GroupApproximation/**/*.lean, Palomar/*.lean, lakefile.toml). Nothing else from the local
# shared tree reaches the build, so a GREEN certifies exactly origin/main@tip + those bytes. Nothing builds here.
#
# Rules: run it with Bash run_in_background: true; ONE probe per lane at a time; BATCH (one probe builds every
# module you land together); never kill a running probe (the remote build holds the clone lock). Probes of all
# lanes serialize on the clone lock, so a probe may wait for others first.
# Evidence: the md5 of every overlay file that COMPILED is recorded with the base SHA, module list and PROBE line,
# in $BC/lanes/<lane>.green.<tag> when the probe is GREEN and in <lane>.failed.<tag> otherwise. A .failed. record
# says what compiled in a failed probe; it is never landing evidence.
# Bytes already recorded GREEN for the same module list are refused (exit 0, ALREADY GREEN) only when no synced path
# changed between that record's base and the current origin/main; BC_FORCE=1 re-certifies regardless.
# Output ends with PROBE GREEN / PROBE FAILED / PROBE DEFERRED (exit 5: clone preparation in progress) and REAL_EXIT=<rc>.
# BC_SRCROOT=<dir> reads the overlay files from <dir>/<repo-relative path> instead of the shared tree (infra calibration
# plants live there, so a deliberately red file never sits in the shared checkout); git and the base SHA still come from the repo.
set -uo pipefail
BC=__SCRATCHPAD__/bc
REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; BCR=$P/bc; CLONE=$P/bc_clones/bc
ROSTER=" bc-pair bc-kazhdan bc-rf kt-norm-paper kt-norm-repo kt-norm-fixedpoint kt-norm-counting bc-dynamics bc-dynamics-upper bc-double-surj bc-wreath bc-assembly bc-palomar bc-review bc-infra "
SYNC_PATHS="GroupApproximation GroupApproximation.lean Palomar lakefile.toml lake-manifest.json lean-toolchain"
usage() { echo "usage: bcprobe.sh <lane> <overlay files...> -- <Module.Name...>"; exit 2; }
LANE=${1:-}; [ -n "$LANE" ] || usage; shift
case "$ROSTER" in *" $LANE "*) ;; *) echo "REFUSED: unknown lane '$LANE'"; exit 2;; esac
FILES=()
while [ $# -gt 0 ] && [ "$1" != "--" ]; do FILES+=("$1"); shift; done
[ "${1:-}" = "--" ] || usage
shift; [ $# -ge 1 ] || usage
MODS="$*"
mkdir -p "$BC/lanes" "$BC/ov"
cd "$REPO" || exit 2
SRCROOT=${BC_SRCROOT:-$REPO}
[ -d "$SRCROOT" ] || { echo "REFUSED: BC_SRCROOT '$SRCROOT' is not a directory"; exit 2; }
git fetch -q origin main 2>/dev/null || { echo "PROBE FAILED: git fetch (infra)"; exit 4; }
SHA=$(git rev-parse --verify -q origin/main) || { echo "PROBE FAILED: cannot resolve origin/main (infra)"; exit 4; }
# Guard (09-12 wipe): never probe against a tree that lacks the library root, the manifest or the lakefile.
for root in GroupApproximation.lean lake-manifest.json lakefile.toml; do
  git cat-file -e "$SHA:$root" 2>/dev/null \
    || { echo "REFUSED: origin/main@${SHA:0:9} lacks $root; not probing against a gutted tree (infra)"; exit 4; }
done
TAG=$(date +%m%d-%H%M%S)-$$
OVL=$BC/ov/$LANE-$TAG; mkdir -p "$OVL"
PEND=$BC/lanes/$LANE.pending-$TAG.md5; : > "$PEND"
cleanup() { rm -rf "$OVL" "$OVL.tgz" "$PEND"; }
for p in ${FILES[@]+"${FILES[@]}"}; do
  case "$p" in
    GroupApproximation/*.lean|Palomar/*.lean|lakefile.toml) ;;
    *) echo "REFUSED: overlay path '$p' (allowed: GroupApproximation/**/*.lean, Palomar/*.lean, lakefile.toml)"; cleanup; exit 2;;
  esac
  [ -f "$SRCROOT/$p" ] || { echo "REFUSED: $p missing under $SRCROOT"; cleanup; exit 2; }
  mkdir -p "$OVL/$(dirname "$p")"; cp "$SRCROOT/$p" "$OVL/$p"
  echo "$(md5 -q "$OVL/$p")  $p" >> "$PEND"
done
for m in $MODS; do
  case "$m" in GroupApproximation.*|Palomar.*) ;; *) echo "REFUSED: module '$m' must start with GroupApproximation. or Palomar."; cleanup; exit 2;; esac
  p="${m//.//}.lean"
  if [ -f "$OVL/$p" ]; then :
  elif ! git cat-file -e "$SHA:$p" 2>/dev/null; then echo "REFUSED: $p is neither an overlay file nor on origin/main@${SHA:0:9}"; cleanup; exit 2; fi
done
if [ -z "${BC_FORCE:-}" ] && [ -s "$PEND" ]; then
  for rec in "$BC"/lanes/"$LANE".green.*; do
    [ -f "$rec" ] || continue
    grep -qxF "# mods $MODS" "$rec" || continue
    grep -qx '# PROBE GREEN' "$rec" || continue
    miss=0
    while IFS= read -r line; do grep -qxF "$line" "$rec" || { miss=1; break; }; done < "$PEND"
    [ $miss -eq 0 ] || continue
    RB=$(sed -n 's/^# base //p' "$rec")
    if [ "$RB" = "$SHA" ] || { git cat-file -e "$RB^{commit}" 2>/dev/null \
         && [ -z "$(git diff --name-only "$RB" "$SHA" -- $SYNC_PATHS | head -1)" ]; }; then
      echo "ALREADY GREEN: these bytes and modules are recorded in $rec at base ${RB:0:9}, and no synced path changed up to ${SHA:0:9}; not re-probing"
      cleanup; exit 0
    fi
    echo "note: $rec certified these bytes at base ${RB:0:9}, but synced paths changed up to ${SHA:0:9}; re-probing"
  done
fi
"$MSI" true >/dev/null 2>&1 || { echo "PROBE FAILED: msi connection down (infra, not Lean)"; cleanup; exit 4; }
tar czf "$OVL.tgz" -C "$OVL" .
OUT0=$("$MSI" "mkdir -p $CLONE/.nm/ov-$TAG && tar xzf - -C $CLONE/.nm/ov-$TAG && sed -e 's|__TAG__|$TAG|' -e 's|__SHA__|$SHA|' -e 's|__MODS__|$MODS|' -e 's|__LANE__|$LANE|' $BCR/bcjob.template.sh > $CLONE/.nm/job-$TAG.sh && echo UPLOAD_OK" < "$OVL.tgz" 2>&1)
printf '%s\n' "$OUT0" | grep -q UPLOAD_OK || { echo "PROBE FAILED: overlay upload (infra): $OUT0"; cleanup; exit 4; }
echo "probe lane=$LANE tag=$TAG base=${SHA:0:9} overlay=$(wc -l < "$PEND" | tr -d ' ') files mods: $MODS"
OUT=$("$MSI" "bash $P/nm/dispatch.sh $CLONE/.nm/job-$TAG.sh $CLONE/.nm/out-$TAG.txt bc-$LANE ${BC_CPUS:-8}" 2>&1); RC=$?
printf '%s\n' "$OUT"
COMP=$(printf '%s\n' "$OUT" | sed -n 's/^COMPILED //p')
PL=$(printf '%s\n' "$OUT" | grep -m1 -E '^PROBE (GREEN|FAILED|DEFERRED)')
if [ -n "$COMP" ]; then
  KIND=failed; [ "$PL" = "PROBE GREEN" ] && KIND=green
  REC=$BC/lanes/$LANE.$KIND.$TAG
  { echo "# base $SHA"; echo "# tag $TAG"; echo "# mods $MODS"; echo "# srcroot $SRCROOT"; echo "# $PL"
    while IFS= read -r line; do p="${line#*  }"; printf '%s\n' "$COMP" | grep -qxF "$p" && echo "$line"; done < "$PEND"; } > "$REC"
  echo "recorded compiled evidence ($(printf '%s\n' "$COMP" | wc -l | tr -d ' ') files): $REC"
  [ "$KIND" = green ] || echo "NOT GREEN: $REC lists what compiled in a failed probe; it is never landing evidence"
fi
[ -n "$PL" ] || echo "PROBE FAILED: no summary came back (msi hop died? rc=$RC). Remote output: $CLONE/.nm/out-$TAG.txt"
echo "REAL_EXIT=$RC"
cleanup
exit $RC
