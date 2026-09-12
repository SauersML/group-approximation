#!/usr/bin/env bash
# nmprobe.sh <lane> <Module.Name> [<Module.Name> ...]
#
# Build the named modules ON MSI in the lane's own clone, against
#   origin/main (current SHA, exported from the MSI mirror)  +  the lane's overlay,
# where the overlay is every repo path listed in  $NM/lanes/<lane>.files
# (one GroupApproximation/**/*.lean path per line: the files the lane owns, new or edited).
# Nothing else from the local shared tree reaches the build, so a GREEN certifies
# exactly origin/main + those bytes.  Nothing is built on this Mac.
#
# Prints the remote summary: per-module BUILT lines, the error index, PROBE GREEN /
# PROBE FAILED / PROBE DEFERRED (exit 5 = clone preparation in progress; author
# meanwhile and retry later).  On GREEN it records the md5 of every overlay file as
# built in $NM/lanes/<lane>.green.<tag>; nmland.sh lands only bytes recorded there.
#
# Run it with Bash run_in_background: true (builds can take many minutes).  One probe
# per lane at a time; never kill a running probe (the remote build keeps the lock).
set -uo pipefail
NM=/private/tmp/claude-501/-Users-user-nonsofic-existence/77122910-de5a-4e59-a488-7cea550292c5/scratchpad/nm
REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; SOCK=/tmp/msi-login.sock; ALIAS=__MSI_LOGIN__
P=/projects/standard/__MSI_GROUP__/__MSI_USER__
LANE=${1:?usage: nmprobe.sh <lane> <Module...>}; shift
[ $# -ge 1 ] || { echo "usage: nmprobe.sh <lane> <Module...>"; exit 2; }
[ -s "$NM/lanes/$LANE.clone" ] || { echo "unknown lane $LANE (no $NM/lanes/$LANE.clone)"; exit 2; }
CLONE=$P/cc_clones/$(cat "$NM/lanes/$LANE.clone")
FILES=$NM/lanes/$LANE.files; touch "$FILES"
TAG=$(date +%m%d-%H%M%S)-$$
MODS="$*"
cd "$REPO" || exit 2
git fetch -q origin main 2>/dev/null || { echo "PROBE FAILED: git fetch (infra)"; exit 4; }
SHA=$(git rev-parse origin/main)
for m in $MODS; do
  case "$m" in GroupApproximation.*) ;; *) echo "REFUSED: module names must start with GroupApproximation. ($m)"; exit 2;; esac
  p="${m//.//}.lean"
  if grep -qxF "$p" "$FILES"; then [ -f "$p" ] || { echo "REFUSED: $p listed but missing locally"; exit 2; }
  elif ! git cat-file -e "$SHA:$p" 2>/dev/null; then echo "REFUSED: $p is neither in $FILES nor on origin/main"; exit 2; fi
done
OVL=$NM/ov/$LANE-$TAG; mkdir -p "$OVL"
PEND=$NM/lanes/$LANE.pending-$TAG.md5; : > "$PEND"
while IFS= read -r p; do
  [ -n "$p" ] || continue
  case "$p" in GroupApproximation/*.lean) ;; *) echo "REFUSED: '$p' in $FILES is not a GroupApproximation/**/*.lean path"; rm -rf "$OVL" "$PEND"; exit 2;; esac
  [ -f "$p" ] || { echo "REFUSED: $p listed in $FILES but missing locally"; rm -rf "$OVL" "$PEND"; exit 2; }
  mkdir -p "$OVL/$(dirname "$p")"; cp "$p" "$OVL/$p"
  echo "$(md5 -q "$OVL/$p")  $p" >> "$PEND"
done < "$FILES"
"$MSI" true >/dev/null 2>&1 || "$MSI" up >/dev/null 2>&1 || { echo "PROBE FAILED: msi connection down (infra, not Lean)"; rm -rf "$OVL" "$PEND"; exit 4; }
RSH="ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR"
for attempt in 1 2 3; do
  rsync -rlc -e "$RSH" --rsync-path="mkdir -p $CLONE/.nm/ov-$TAG && rsync" "$OVL/" "$ALIAS:$CLONE/.nm/ov-$TAG/" && break
  [ $attempt -eq 3 ] && { echo "PROBE FAILED: overlay upload (infra)"; rm -rf "$OVL" "$PEND"; exit 4; }
  sleep 5
done
sed -e "s|__CLONE__|$CLONE|" -e "s|__TAG__|$TAG|" -e "s|__SHA__|$SHA|" -e "s|__MODS__|$MODS|" "$NM/remote/job.template.sh" > "$OVL.job.sh"
rsync -lc -e "$RSH" "$OVL.job.sh" "$ALIAS:$CLONE/.nm/job-$TAG.sh" || { echo "PROBE FAILED: job upload (infra)"; exit 4; }
echo "probe lane=$LANE tag=$TAG base=${SHA:0:9} overlay=$(wc -l < "$PEND" | tr -d ' ') files mods: $MODS"
OUT=$("$MSI" "bash $P/nm/dispatch.sh $CLONE/.nm/job-$TAG.sh $CLONE/.nm/out-$TAG.txt nm-$LANE ${NM_CPUS:-8}" 2>&1); RC=$?
printf '%s\n' "$OUT"
COMP=$(printf '%s\n' "$OUT" | sed -n 's/^COMPILED //p')
if [ -n "$COMP" ]; then
  # evidence = only overlay files that actually COMPILED in this build (even if other modules failed)
  { echo "# base $SHA"; echo "# tag $TAG"; echo "# mods $MODS"; echo "# $(printf '%s\n' "$OUT" | grep -m1 -E '^PROBE ')";
    while IFS= read -r line; do p="${line#*  }"; printf '%s\n' "$COMP" | grep -qxF "$p" && echo "$line"; done < "$PEND"; } > "$NM/lanes/$LANE.green.$TAG"
  echo "recorded compiled evidence ($(printf '%s\n' "$COMP" | wc -l | tr -d ' ') files): $NM/lanes/$LANE.green.$TAG"
fi
if ! printf '%s\n' "$OUT" | grep -qE '^PROBE (GREEN|FAILED|DEFERRED)'; then
  echo "PROBE FAILED: no summary came back (msi hop died? rc=$RC). Remote output: $CLONE/.nm/out-$TAG.txt"
fi
rm -rf "$OVL" "$OVL.job.sh" "$PEND"
exit $RC
