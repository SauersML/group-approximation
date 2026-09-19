#!/bin/bash
# bh-pal-wire upstream probe: is the other session's chain under FrontierFour green yet?
# Read-only on the shared checkout.  At most one run per hour (coordinator order, 09-18).
# 1. Recompute the import closure of FrontierFour's seven direct imports from the working tree.
# 2. If a leaf red module (only Mathlib + AxiomGuard imports) is still in that closure with the
#    same source as when it last failed, it is certainly still red: print SKIP and build nothing.
# 3. Otherwise run one trusted, mutexed probe build of the seven endpoints via
#    scripts/remote-build.sh, record the new red set, and print UPSTREAM GREEN or STILL RED.
set -u
W=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq/work/bh-pal-wire
REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi
RLOG=/projects/standard/hsiehph/sauer354/nonsofic_existence/.lake/last-build-bhpalwire-probe.log
TOPS="GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierThree GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierTwo GroupApproximation.BooneHigman.Products.Hosts GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEWire GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellEndpoint GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormFinal GroupApproximation.BooneHigman.Metabelian.EnvelopeVPerfect"
cd "$REPO" || exit 3
modpath() { echo "$1" | tr . /; }
echo "probe start $(date '+%Y-%m-%d %H:%M %Z')"

# 1. closure
printf '%s\n' $TOPS > "$W/p.fr"; : > "$W/p.seen"
while [ -s "$W/p.fr" ]; do
  cat "$W/p.fr" >> "$W/p.seen"; : > "$W/p.nx"
  while read -r m; do
    f="$(modpath "$m").lean"
    [ -f "$f" ] && awk '/^import GroupApproximation/{print $2}' "$f" >> "$W/p.nx"
  done < "$W/p.fr"
  sort -u "$W/p.nx" | comm -23 - <(sort -u "$W/p.seen") > "$W/p.fr"
done
sort -u "$W/p.seen" > "$W/p.closure"
echo "closure: $(wc -l < "$W/p.closure" | tr -d ' ') modules"

# 2. certain-red shortcut
if [ "$(md5 -q GroupApproximation/Meta/AxiomGuard.lean)" = "$(cat "$W/axiomguard.md5")" ]; then
  while read -r h m; do
    grep -qx "$m" "$W/p.closure" || continue
    if [ "$(md5 -q "$(modpath "$m").lean" 2>/dev/null)" = "$h" ]; then
      echo "SKIP: leaf red $m is unchanged and still in the closure; no build"
      exit 0
    fi
  done < "$W/leafred.md5"
fi

# 3. trusted probe build; snapshot sources first so the baseline is what the build saw
while read -r m; do
  f="$(modpath "$m").lean"; [ -f "$f" ] && echo "$(md5 -q "$f") $m"
done < "$W/p.closure" > "$W/p.pre.md5"
md5 -q GroupApproximation/Meta/AxiomGuard.lean > "$W/p.pre.ag"
START=$(date +%s)
MSI_BUILD_TAG=bhpalwire-probe MSI_BUILD_CORES=32 timeout 5400 scripts/remote-build.sh "$TOPS" \
  > "$W/probe-build.log" 2>&1
rc=$?
echo "build rc=$rc (local log $W/probe-build.log)"
"$MSI" "L=$RLOG; stat -c %Y \$L; echo ==; awk '/^Some required targets logged failures:/{f=1;next} f && /^- /{print \$2}' \$L | sort -u; echo ==; tail -2 \$L; echo SENTINEL" \
  < /dev/null 2>&1 | tr -d '\r' > "$W/p.remote"
grep -qx SENTINEL "$W/p.remote" || { echo "remote read failed; baseline unchanged"; exit 4; }
MT=$(head -1 "$W/p.remote")
if [ "$MT" -lt "$START" ] 2>/dev/null; then
  echo "remote log predates this probe (mtime $MT < start $START): build never ran; baseline unchanged"
  exit 5
fi
awk '/^==$/{s++; next} s==1' "$W/p.remote" | grep -v '^$' > "$W/p.red"
echo "remote log tail: $(awk '/^==$/{s++; next} s==2' "$W/p.remote" | grep -v SENTINEL | tr '\n' ' ')"
if [ "$rc" = 0 ] && [ ! -s "$W/p.red" ]; then
  echo "UPSTREAM GREEN: all seven FrontierFour imports built on MSI"
  exit 0
fi
echo "STILL RED: $(wc -l < "$W/p.red" | tr -d ' ') modules logged failures"
[ -s "$W/p.red" ] || { echo "no failure list (rc=$rc); baseline unchanged"; exit 6; }
# new baseline: the red set, and the leaf reds among them with their pre-build md5
cp "$W/p.red" "$W/red.txt"
cp "$W/p.pre.ag" "$W/axiomguard.md5"
: > "$W/leafred.md5"
while read -r m; do
  f="$(modpath "$m").lean"
  n=$(awk '/^import GroupApproximation/{print $2}' "$f" 2>/dev/null | grep -vx 'GroupApproximation.Meta.AxiomGuard' | wc -l | tr -d ' ')
  [ "$n" = 0 ] && grep " $m\$" "$W/p.pre.md5" >> "$W/leafred.md5"
done < "$W/red.txt"
echo "leaf reds now: $(wc -l < "$W/leafred.md5" | tr -d ' ')"
exit 0
