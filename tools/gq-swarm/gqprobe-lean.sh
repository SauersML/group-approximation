#!/usr/bin/env bash
# gqprobe-lean.sh <lane> <Module.Name> [<Module.Name> ...]      (v4, 09-18 ~16:45: BATCHED Slurm probes)
#
# Trusted Lean probe for gq/bh/ms/fix lanes. Same interface and verdicts as before. Nothing builds on this Mac.
#   overlay = every repo-relative path listed (one per line) in $GQ/work/<lane>/overlay.files,
#             copied from $GQ/work/<lane>/<path>.
# How it works:
#   1. The request (targets + a frozen copy of the overlay bytes) goes into $GQ/state/pq/<id>/.
#   2. Whoever holds $GQ/state/msi-build.lock is the BUILDER. It drains up to 10 queued requests whose overlays
#      don't conflict (same path, different bytes => wait for the next batch), exports origin/main + the union of
#      those overlays, syncs to the warm dir ONCE (rsync --checksum), and submits ONE Slurm job. The job runs a
#      separate `lake build <targets>` for each request in turn, so every lane gets its own exact rc and error
#      index.
#   3. Each request's verdict lands in $GQ/state/pq/<id>/result. On GREEN, the frozen overlay bytes are recorded
#      in $GQ/state/green/<lane>.<epoch>, and gqland-lean-green.sh accepts exactly those bytes.
# Note: a batched build sees the other requests' overlays too, i.e. "main + pending fixes". The record says so.
# Verdicts: PROBE GREEN / PROBE FAILED (error index) / PROBE DEFERRED (queue or MSI trouble; re-probe later).
# Run with Bash run_in_background: true. Keep targets narrow and never build the whole library.
set -uo pipefail
GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq
REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; SOCK=/tmp/msi-login.sock; ALIAS=login.msi.umn.edu
MUSER=sauer354; LOGIN=128.101.190.100
PHOME=/projects/standard/hsiehph/sauer354; REMOTE=$PHOME/nonsofic_existence
PQ=$GQ/state/pq
LANE=${1:?usage: gqprobe-lean.sh <lane> <Module.Name...>}; shift
[ $# -ge 1 ] || { echo "usage: gqprobe-lean.sh <lane> <Module.Name...>"; exit 2; }
W=$GQ/work/$LANE; OV=$W/overlay.files
[ -f "$OV" ] || { echo "REFUSED: create $OV (one repo path per line; may be empty to probe origin/main as is)"; exit 2; }
for m in "$@"; do
  echo "$m" | grep -qE '^[A-Za-z0-9_.]+$' || { echo "REFUSED: bad module name '$m'"; exit 2; }
  [ "$m" = GroupApproximation ] && { echo "REFUSED: never build the whole library; name your modules"; exit 2; }
done
while read -r p; do
  [ -z "$p" ] && continue
  case "$p" in
    /*|*..*) echo "REFUSED: bad overlay path '$p'"; exit 2;;
    scripts/remote-build.*) echo "REFUSED: the build driver cannot be overlaid"; exit 2;;
  esac
  [ -f "$W/$p" ] || { echo "REFUSED: overlay file missing: $W/$p"; exit 2; }
done < "$OV"
AVAIL_KB=$(df -k /System/Volumes/Data | awk 'NR==2{print $4}')
[ "${AVAIL_KB:-0}" -ge 1572864 ] || { echo "PROBE DEFERRED: under 1.5 GiB free on the Mac; tell team-lead"; exit 5; }
mkdir -p "$PQ" "$GQ/state/green" "$GQ/state/probe-logs"
msi() { "$MSI" "$@" < /dev/null 2>&1 | tr -d '\r'; }

# ---- 1. enqueue (frozen copy of the overlay bytes)
ID="$(date +%s).$$.$LANE"; R=$PQ/$ID; mkdir -p "$R/files"
echo "$LANE" > "$R/lane"; echo "$*" > "$R/targets"; : > "$R/overlay.md5"
while read -r p; do
  [ -z "$p" ] && continue
  mkdir -p "$R/files/$(dirname "$p")"; cp "$W/$p" "$R/files/$p"
  echo "$(md5 -q "$R/files/$p") $p" >> "$R/overlay.md5"
done < "$OV"
touch "$R/ready"
echo "$(date '+%H:%M:%S') queued probe $ID ($(wc -l < "$R/overlay.md5" | tr -d ' ') overlay files; targets $*)"

# ---- 2. builder: drain one batch while holding the lock
build_batch() {
  local BASE SNAP LIST=() r p h seen JOBF JLOG SUB JID ST fails PSTART i OUT
  cd "$REPO" || return 1
  for f in 1 2 3; do timeout 60 git fetch -q origin main 2>/dev/null && break; sleep 3; done
  BASE=$(git rev-parse refs/remotes/origin/main) || return 1
  seen=$(mktemp "$GQ/state/.seen.XXXXXX")
  for r in $(ls -d "$PQ"/*/ 2>/dev/null | sed 's:/$::' | sort | head -40); do
    [ -f "$r/ready" ] && [ ! -f "$r/result" ] && [ ! -f "$r/taken" ] || continue
    ok=1
    while read -r h p; do
      q=$(awk -v p="$p" '$2==p{print $1}' "$seen" | head -1)
      [ -n "$q" ] && [ "$q" != "$h" ] && { ok=0; break; }
    done < "$r/overlay.md5"
    [ $ok = 1 ] || continue
    cat "$r/overlay.md5" >> "$seen"; LIST+=("$r"); touch "$r/taken"
    [ ${#LIST[@]} -ge 10 ] && break
  done
  rm -f "$seen"
  [ ${#LIST[@]} -ge 1 ] || return 0
  echo "builder $$ batch of ${#LIST[@]} $(date '+%H:%M:%S')" > "$GQ/state/msi-build.holder"
  SNAP=$GQ/snap; rm -rf "$SNAP"; mkdir -p "$SNAP"
  local PARTS=""
  for p in GroupApproximation GroupApproximation.lean lean-toolchain lakefile.toml lake-manifest.json Palomar scripts; do
    git cat-file -e "$BASE:$p" 2>/dev/null && PARTS="$PARTS $p"
  done
  # shellcheck disable=SC2086
  git archive "$BASE" $PARTS | tar -x -C "$SNAP" || { rm -rf "$SNAP"; for r in "${LIST[@]}"; do rm -f "$r/taken"; done; return 1; }
  mkdir -p "$SNAP/Palomar" "$SNAP/scripts"
  for r in "${LIST[@]}"; do ( cd "$r/files" && find . -type f | while read -r f; do mkdir -p "$SNAP/$(dirname "$f")"; cp "$f" "$SNAP/$f"; done ); done
  msi 'true' >/dev/null
  local RSH="ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR" syncok=1
  for a in 1 2 3; do
    rsync -rlpcz --delete -e "$RSH" --include='*/' --include='*.lean' --exclude='*' \
      "$SNAP/GroupApproximation/" "$MUSER@$LOGIN:$REMOTE/GroupApproximation/" \
    && rsync -rlpcz -e "$RSH" "$SNAP/GroupApproximation.lean" "$SNAP/lean-toolchain" "$SNAP/lakefile.toml" \
         "$SNAP/lake-manifest.json" "$MUSER@$LOGIN:$REMOTE/" \
    && rsync -rlpcz --delete -e "$RSH" --include='*/' --include='*.lean' --include='*.json' --exclude='*' \
         "$SNAP/Palomar/" "$MUSER@$LOGIN:$REMOTE/Palomar/" \
    && rsync -rlpcz -e "$RSH" --include='*/' --include='*.lean' --exclude='*' \
         "$SNAP/scripts/" "$MUSER@$LOGIN:$REMOTE/scripts/" \
    && { syncok=0; break; }
    sleep 10; msi 'true' >/dev/null
  done
  rm -rf "$SNAP"
  if [ $syncok -ne 0 ]; then
    for r in "${LIST[@]}"; do echo "PROBE DEFERRED: source sync to MSI failed (VPN/master?)" > "$r/result.tmp"; mv "$r/result.tmp" "$r/result"; done
    return 1
  fi
  # one Slurm job, one lake build per request
  local B="b$(date +%s)"; JOBF=$PHOME/gq-slurm/batch-$B.sbatch
  local BODY="" n=0
  for r in "${LIST[@]}"; do
    n=$((n+1)); BODY="$BODY
echo '===== REQ $n ====='; lake build $(cat "$r/targets") > $PHOME/gq-slurm/batch-$B-$n.log 2>&1; echo \"RC_$n \$?\""
  done
  SUB=$(msi "mkdir -p $PHOME/gq-slurm && cat > $JOBF <<'EOS'
#!/bin/bash
#SBATCH -p ag2tb,msismall,msilarge,aglarge,agsmall
#SBATCH -c 8
#SBATCH --mem=48G
#SBATCH --time=01:30:00
#SBATCH -J gq-batch-$n
#SBATCH --output=$PHOME/gq-slurm/batch-$B.out
export HOME=$PHOME XDG_CACHE_HOME=$PHOME/.cache PATH=$PHOME/.elan/bin:\$PATH LEAN_NUM_THREADS=8
cd $REMOTE || exit 3
exec 9>.lake/fleet-build.lock
flock -w 3600 9 || { echo 'fleet build lock: timed out'; exit 75; }
echo \"start \$(date) on \$(hostname)\"$BODY
echo '===== BATCH DONE'
EOS
sbatch --parsable $JOBF")
  JID=$(echo "$SUB" | grep -oE '^[0-9]+' | tail -1)
  if [ -z "$JID" ]; then
    for r in "${LIST[@]}"; do echo "PROBE DEFERRED: sbatch failed: $SUB" > "$r/result.tmp"; mv "$r/result.tmp" "$r/result"; done
    return 1
  fi
  echo "builder $$ batch of ${#LIST[@]} slurm $JID $(date '+%H:%M:%S')" > "$GQ/state/msi-build.holder"
  ST=""; fails=0; PSTART=$(date +%s)
  for i in $(seq 1 600); do
    sleep 20
    ST=$(msi "sacct -j $JID -X -n -P -o State 2>/dev/null | head -1" | grep -oE '^[A-Z_]+' | head -1)
    [ -z "$ST" ] && { fails=$((fails+1)); [ $fails -gt 30 ] && break; continue; }
    if [ "$ST" = PENDING ] && [ $(($(date +%s) - PSTART)) -gt 1200 ]; then msi "scancel $JID" >/dev/null; ST=PENDING_TIMEOUT; break; fi
    [ "$ST" = RUNNING ] && PSTART=9999999999
    case "$ST" in PENDING|RUNNING|REQUEUED|CONFIGURING|COMPLETING|SUSPENDED) continue;; *) break;; esac
  done
  local RCS; RCS=$(msi "grep -E '^RC_[0-9]+ ' $PHOME/gq-slurm/batch-$B.out; echo SENTINEL")
  n=0
  for r in "${LIST[@]}"; do
    n=$((n+1)); local L="$GQ/state/probe-logs/$(cat "$r/lane").$(date +%s).$n.log"
    rc=$(echo "$RCS" | awk -v k="RC_$n" '$1==k{print $2}')
    OUT=$(msi "L=$PHOME/gq-slurm/batch-$B-$n.log; echo '===== ERROR INDEX ====='; grep -anE 'error:|declaration uses' \$L | head -60; echo '===== CONTEXT (from first error) ====='; awk '/error:/{f=1} f' \$L | head -200; echo '===== STATUS ====='; tail -4 \$L; echo SENTINEL")
    { echo "base $BASE; batch job $JID ($n of ${#LIST[@]}); state $ST; rc ${rc:-none}"; echo "$OUT"; } > "$L"
    ERRS=$(echo "$OUT" | awk '/===== ERROR INDEX =====/{f=1;next} /===== CONTEXT/{f=0} f' | grep -c 'error:')
    SORRY=$(echo "$OUT" | grep -c "declaration uses 'sorry'")
    if [ "$ST" = PENDING_TIMEOUT ]; then V="PROBE DEFERRED: batch Slurm job $JID pended >20 min; cancelled. Re-probe later. log=$L"
    elif [ "${rc:-x}" = 0 ] && [ "$ERRS" -eq 0 ] && echo "$OUT" | grep -q SENTINEL; then
      G=$GQ/state/green/$(cat "$r/lane").$(date +%s).$n
      { echo "base $BASE (batched with ${#LIST[@]} requests; main + pending fixes)"; echo "targets $(cat "$r/targets")"; cat "$r/overlay.md5"; } > "$G"
      V="PROBE GREEN job=$JID sorry_warnings=$SORRY record=$G log=$L"
    elif [ -z "${rc:-}" ]; then V="PROBE DEFERRED: lost contact or job ended early (state '$ST'); check sacct -j $JID. log=$L"
    else V="PROBE FAILED job=$JID rc=$rc errors=$ERRS sorry_warnings=$SORRY log=$L"; fi
    { echo "$V"; [ "${V#PROBE FAILED}" != "$V" ] && echo "$OUT" | awk '/===== ERROR INDEX =====/{f=1} f' | head -80; } > "$r/result.tmp"
    mv "$r/result.tmp" "$r/result"
  done
  return 0
}

# ---- 3. wait for my verdict; build batches whenever the lock is free
exec 8>"$GQ/state/msi-build.lock"
for t in $(seq 1 1440); do
  if [ -f "$R/result" ]; then
    cat "$R/result"
    head -1 "$R/result" | grep -q '^PROBE GREEN' && exit 0
    head -1 "$R/result" | grep -q '^PROBE DEFERRED' && exit 5
    exit 1
  fi
  if flock -n 8; then build_batch; flock -u 8; continue; fi
  sleep 15
done
echo "PROBE DEFERRED: no verdict after 6 h (request $ID left in queue)"; exit 5
