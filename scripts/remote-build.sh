#!/usr/bin/env bash
# Sync the local tree to the warm remote build dir and run `lake build` there.
#
#   scripts/remote-build.sh              sync + build the default target
#   scripts/remote-build.sh Audit        sync + build a specific target
#   scripts/remote-build.sh --sync-only  just push the files
#   scripts/remote-build.sh --audit      sync + run the kernel audit
#   scripts/remote-build.sh --run FILE   sync + `lake env lean FILE` on the node
#
# The kernel audit needs a built environment, which since the local .lake was
# removed exists only on the node.  Without a mode here it was the awkward one
# to run -- and it is the half that asks whether the theorems say what they are
# meant to say, so it must not be the half that gets skipped.  `check.py` is
# the other half and runs anywhere.
#
# Only sources are synced: .lake/ (the warm olean cache, ~GBs of mathlib) and
# the git metadata stay put on the remote.  Everything runs on the compute node
# via the wrapper's ControlMaster; nothing is built locally.
#
# SITE CONFIGURATION lives outside this file, because it is one person's
# cluster account (paths, username, login host) in a public repository -- not a
# secret, but not repository knowledge either.  Everything below IS repository
# knowledge: the import-closure orphan scan, the >50 tripwire, the fleet mutex,
# the post-rsync touch that defeats mtime cache poisoning, the per-invocation
# log tag.  That half had a serious bug on 2026-08-16 that nobody could review
# because the whole script was gitignored, which is why the two are now split.
set -uo pipefail

# Resolve config: the environment wins, then scripts/remote-build.env beside
# this script, then fail with the names that are missing.  Failing loudly beats
# a fresh clone silently getting nothing, which is the state this replaces.
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SITE_VARS="MSI_WRAPPER MSI_LOCAL_ROOT MSI_REMOTE_ROOT MSI_SSH_SOCKET
           MSI_SSH_ALIAS MSI_USER MSI_LOGIN_HOST"

# The environment wins over the file, so a single session can point one
# invocation at a scratch checkout without editing shared state.  Sourcing
# alone would give the file the last word, which is the opposite -- so stash
# whatever the environment already set and put it back afterwards.
for v in $SITE_VARS; do eval "__env_$v=\${$v:-}"; done
[ -f "$HERE/remote-build.env" ] && . "$HERE/remote-build.env"
for v in $SITE_VARS; do
  eval "__e=\${__env_$v}"
  [ -n "${__e:-}" ] && eval "$v=\$__e"
done

MISSING=""
for v in $SITE_VARS; do
  [ -z "${!v:-}" ] && MISSING="$MISSING $v"
done
if [ -n "$MISSING" ]; then
  echo "remote-build: missing site configuration:$MISSING" >&2
  echo "  Set them in the environment, or copy scripts/remote-build.env.example" >&2
  echo "  to scripts/remote-build.env and fill it in (that file is gitignored)." >&2
  exit 2
fi

MSI="$MSI_WRAPPER"
LOCAL="$MSI_LOCAL_ROOT"
REMOTE="$MSI_REMOTE_ROOT"
SOCK="$MSI_SSH_SOCKET"
ALIAS="$MSI_SSH_ALIAS"
USER_MSI="$MSI_USER"
LOGIN_IP="$MSI_LOGIN_HOST"

SYNC_ONLY=0
AUDIT=0
RUN=""
[ "${1:-}" = "--sync-only" ] && { SYNC_ONLY=1; shift; }
[ "${1:-}" = "--audit" ] && { AUDIT=1; shift; }
# The custody scripts -- `scripts/Signatures.lean`, `scripts/StatementClosure.lean`
# -- are `lake env lean` drivers like the audit, and they WRITE their generated
# snapshots into the tree they run in.  That tree is the remote one, so the
# result has to be copied back; `--run` does both, and refuses a path outside
# `scripts/` so this never becomes a way to execute arbitrary remote files.
if [ "${1:-}" = "--run" ]; then
  RUN="${2:-}"
  case "$RUN" in
    scripts/*.lean) ;;
    *) echo "remote-build: --run takes a scripts/*.lean driver, got '${RUN:-}'" >&2; exit 2 ;;
  esac
  shift 2
fi
TARGET="${1:-}"

# rsync cannot re-auth on its own, so the master has to be up before we sync.
# Let the wrapper own that entirely: a plain command self-heals an expired
# master, and `msi up` is its explicit (re)establish.  Never poke at the
# wrapper's auth lock from here -- its lock/cooldown/breaker logic is what
# keeps a fleet of sessions from all triggering Duo at once, and its own
# messages are more informative than anything we would print instead.
"$MSI" true >/dev/null 2>&1 || "$MSI" up || exit 1

echo "==> syncing sources to $REMOTE"
rsync -rlptz --delete \
  -e "ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR" \
  --include='*/' \
  --include='*.lean' --include='lean-toolchain' --include='lakefile.toml' \
  --include='lake-manifest.json' \
  --exclude='*' \
  "$LOCAL/GroupApproximation/" "$USER_MSI@$LOGIN_IP:$REMOTE/GroupApproximation/" || exit $?

rsync -rlptz \
  -e "ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR" \
  "$LOCAL/GroupApproximation.lean" \
  "$LOCAL/lean-toolchain" \
  "$LOCAL/lakefile.toml" "$LOCAL/lake-manifest.json" \
  "$LOCAL/non_mf_groups_exist.tex" \
  "$LOCAL/README.md" \
  "$USER_MSI@$LOGIN_IP:$REMOTE/" || exit $?

rsync -rlptz --delete \
  -e "ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR" \
  --include='*/' --include='*.md' --include='*.txt' --include='*.json' \
  --exclude='*' \
  "$LOCAL/notes/" "$USER_MSI@$LOGIN_IP:$REMOTE/notes/" || exit $?

# The Palomar submission surface is two Lean libraries in the default target
# set (`PalomarChallenge`, `PalomarSolution`), so without this stanza the
# default build fails on the node with "some modules have bad imports" -- the
# module files simply are not there.  The `.json` include carries
# `comparator.json` along, which is what names those two modules.
rsync -rlptz --delete \
  -e "ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR" \
  --include='*/' --include='*.lean' --include='*.json' --exclude='*' \
  "$LOCAL/Palomar/" "$USER_MSI@$LOGIN_IP:$REMOTE/Palomar/" || exit $?

# The proof ledger and its gate inputs live under metadata/; without this
# stanza the ledger checker cannot run on the remote at all.
rsync -rlptz --delete \
  -e "ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR" \
  --include='*/' --include='*.md' --include='*.txt' --include='*.json' \
  --exclude='*' \
  "$LOCAL/metadata/" "$USER_MSI@$LOGIN_IP:$REMOTE/metadata/" || exit $?

# `*.sh` too: the Palomar statement-match check is a shell script that runs
# `lake env lean` on the node, and a checker that cannot reach the node is a
# checker that never runs.
rsync -rlptz --delete \
  -e "ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR" \
  --include='*/' --include='*.lean' --include='*.py' --include='*.sh' \
  --exclude='*' \
  "$LOCAL/scripts/" "$USER_MSI@$LOGIN_IP:$REMOTE/scripts/" || exit $?

# rsync -t preserves each session's LOCAL mtimes, so a synced file can land
# with an mtime older than lake's last trace and be invisible to lake's
# mtime-keyed hash cache -- lake then compiles against a stale olean.
# (Diagnosed 2026-08-14: 60+ phantom errors from a pre-ef97ae1e olean that
# lake believed current.)  Touch every synced source so lake re-hashes them;
# unchanged content hashes rebuild nothing, so this costs seconds.
"$MSI" "cd $REMOTE && find GroupApproximation scripts Palomar -name '*.lean' -exec touch {} + && \
  touch GroupApproximation.lean lean-toolchain lakefile.toml lake-manifest.json" \
  || exit $?

[ "$SYNC_ONLY" = 1 ] && { echo "==> sync only, done"; exit 0; }

# How much of the Sioux host one build may use.  Both hosts are 128-core EPYC.
#
# This was 8 cores and 8 threads, chosen on 2026-08-14 when several sessions
# built CONCURRENTLY and each lean process spawned workers for all 128 cores,
# producing load ~3749 and "failed to create thread".  The same commit added
# the fleet mutex below, and the mutex is what actually fixed that: at most one
# `lake` runs across the whole fleet now.  With serialization in place an
# 8-core cap is not traffic control, it is leaving 94% of an otherwise idle
# node unused -- measured 2026-08-17, acn112 at load 0.13 with the lock free.
#
# 48 of 128 leaves the majority of the host for other users while giving the
# one build that is allowed to run at a time a useful share.  Override with
# MSI_BUILD_CORES; keep it well under 128 so a second tenant is never starved,
# and never raise it in a way that outlives the mutex.
CORES="${MSI_BUILD_CORES:-48}"
LAST_CORE=$((CORES - 1))

if [ "$AUDIT" = 1 ]; then
  echo "==> kernel audit on the compute node"
  exec "$MSI" "export PATH=\$HOME/.elan/bin:\$PATH LEAN_NUM_THREADS=$CORES && cd $REMOTE && \
    taskset -c 0-$LAST_CORE lake env lean scripts/Audit.lean"
fi

if [ -n "$RUN" ]; then
  echo "==> running $RUN on the compute node"
  "$MSI" "export PATH=\$HOME/.elan/bin:\$PATH LEAN_NUM_THREADS=$CORES && cd $REMOTE && \
    taskset -c 0-$LAST_CORE lake env lean $RUN" || exit $?
  # Pull back whatever the driver regenerated.  Only metadata/ is generated by
  # these drivers, and copying just that keeps a remote tree that has drifted
  # from overwriting sources here.
  # `-u` (skip files newer on this side) so that a peer editing metadata/ in
  # this shared checkout while the driver runs does not get clobbered by the
  # copy that went up a minute earlier.
  echo "==> retrieving regenerated metadata/"
  rsync -rlptzu \
    -e "ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR" \
    --include='*/' --include='*.md' --include='*.txt' --include='*.json' \
    --exclude='*' \
    "$USER_MSI@$LOGIN_IP:$REMOTE/metadata/" "$LOCAL/metadata/" || exit $?
  exit 0
fi

# The lean_lib root is `GroupApproximation`, so `lake build` only reaches
# modules that the root transitively imports.  A new module nobody imports is
# silently skipped and the build still reports success -- which looks exactly
# like "it compiles".  Name those orphans and build them explicitly so green
# always means every module compiled.
#
# "Nobody imports it" means outside the root's TRANSITIVE closure.  This used to
# test for a *direct* `import GroupApproximation.<m>` line in the root module,
# which every legitimately transitive module fails -- so a no-argument
# invocation named hundreds of targets and rebuilt the whole corpus while
# holding the fleet lock, blocking every other lane (2026-08-16: ~300 targets,
# two lanes queued, ten minutes before it was caught).  `scripts/check.py`
# already walks the real closure and gates CI on the answer, so ask it rather
# than keeping a second, wrong opinion here.  The node's default python3 is
# 3.6 and too old; 3.11 is present without a module load.
ORPHANS=""
if [ -z "$TARGET" ]; then
  ORPHANS="$("$MSI" "cd $REMOTE && /usr/bin/python3.11 scripts/check.py --list-orphans" \
    | tr -d '\r' | awk 'NF' | tr '\n' ' ')" || exit $?
  ORPHANS="${ORPHANS% }"
  # A closure scan that suddenly calls most of the library orphaned is broken,
  # not informative -- and acting on it is exactly the full-corpus build this
  # rewrite exists to prevent.  Stop and say so instead of building the world.
  COUNT=$(printf '%s' "$ORPHANS" | wc -w | tr -d ' ')
  if [ "$COUNT" -gt 50 ]; then
    echo "==> refusing to build: the orphan scan returned $COUNT modules, which means" >&2
    echo "    it is broken, not that the library is.  Check scripts/check.py" >&2
    echo "    --list-orphans, or name an explicit target." >&2
    exit 1
  fi
  [ -n "$ORPHANS" ] && ORPHANS=" $ORPHANS"
  [ -n "$ORPHANS" ] && echo "==> outside the root import closure, building separately:$ORPHANS"
fi

# Naming ANY target suppresses lake's default target, so `lake build <orphan>`
# would build only that orphan and its imports -- reporting a cheerful low job
# count while the rest of the corpus went unchecked.  When we add orphans we
# must therefore name the default root explicitly alongside them.
BUILD_TARGETS="$TARGET"
[ -z "$BUILD_TARGETS" ] && [ -n "$ORPHANS" ] && BUILD_TARGETS="GroupApproximation"
BUILD_TARGETS="$BUILD_TARGETS$ORPHANS"

# Lake 5 has no -j flag; taskset is what caps concurrency on the shared node.
# The share is $CORES, set above -- see the rationale there for why it is no
# longer 8.
#
# Do NOT pipe lake through `tail`: it both masks the exit status and silently
# drops the *earliest* errors, which are the ones that matter (a later failure
# is usually a knock-on of the first).  Capture the whole log on shared storage
# instead, then print an index of every error followed by bounded context.
# Per-invocation log: a fleet of sessions shares this script and one log path
# means the error index you read may be another session's build.  Tag the log
# by caller pid (override with MSI_BUILD_TAG for a stable per-session name).
TAG="${MSI_BUILD_TAG:-$$}"
# Fleet traffic control (load-3749 incident, 2026-08-14): taskset caps CORES
# but not THREADS -- each lean process spawns workers for every core it
# detects, so several concurrent sessions produce a four-digit load and
# "failed to create thread".  Two fixes: LEAN_NUM_THREADS caps each process,
# and an atomic mkdir mutex serializes builds across the whole fleet (stale
# locks older than 90 min are broken; waiters give up after 60 min).
#
# The waiter prints on EVERY pass, not every fifteenth.  It used to announce
# itself once and then sit silent for five minutes at a time, and the wrapper's
# ssh carries no ServerAliveInterval -- so a waiting build did not wait, it got
# its connection dropped and came back as exit 255 with a single "waiting on
# fleet build lock (1/180)" above it.  That reads like an ssh fault and is
# really "another lane holds the lock", which is the one thing the message was
# supposed to tell you.  A line every 20s keeps the channel warm; 180 lines is
# the worst case and only if you really do wait an hour.
LOCK=$REMOTE/.lake/fleet-build.lock
echo "==> building${TARGET:+ $TARGET} on the compute node (log tag: $TAG)"
exec "$MSI" "export PATH=\$HOME/.elan/bin:\$PATH LEAN_NUM_THREADS=$CORES && cd $REMOTE && \
  tries=0; until mkdir \"$LOCK\" 2>/dev/null; do \
    age=\$(( \$(date +%s) - \$(stat -c %Y \"$LOCK\" 2>/dev/null || date +%s) )); \
    if [ \$age -gt 5400 ]; then rmdir \"$LOCK\" 2>/dev/null; continue; fi; \
    tries=\$((tries+1)); \
    if [ \$tries -gt 180 ]; then echo 'fleet build lock: timed out after 60m'; exit 75; fi; \
    echo \"waiting on fleet build lock (\$tries/180)\"; \
    sleep 20; \
  done; \
  trap 'rmdir \"$LOCK\" 2>/dev/null' EXIT INT TERM; \
  LOG=$REMOTE/.lake/last-build-$TAG.log && \
  taskset -c 0-$LAST_CORE lake build $BUILD_TARGETS > \"\$LOG\" 2>&1; rc=\$? ; \
  echo '===== ERROR INDEX =====' ; \
  grep -anE 'error:|declaration uses|warning:' \"\$LOG\" | head -60 ; \
  echo '===== CONTEXT (from first error) =====' ; \
  awk '/error:/{f=1} f' \"\$LOG\" | head -250 ; \
  echo '===== STATUS =====' ; \
  tail -4 \"\$LOG\" ; \
  exit \$rc"
