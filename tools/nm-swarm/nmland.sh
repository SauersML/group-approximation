#!/usr/bin/env bash
# nmland.sh <lane> <msgfile> <path> [<path> ...]
#
# Land the given repository paths on origin/main as ONE commit built from the CURRENT
# origin/main tree with a private index (never the shared index, HEAD, a branch, or refs/heads).
# Guards:
#   * refuses GroupApproximation.lean (the lead wires the root);
#   * refuses a .lean with a lexical sorry / admit / axiom outside comments;
#   * every GroupApproximation/**/*.lean being landed must match, byte for byte, ONE green
#     probe record of this lane ($NM/lanes/<lane>.green.*): edit after green => re-probe;
#   * every GroupApproximation import of a landed file must be on origin/main or in this call,
#     and if the green build used an EDITED version of an imported file, that file must be
#     landed in the same call;
#   * the commit may touch exactly the given paths.
# Non-Lean paths (notes, metadata) need no probe record.  Appends to $NM/landed.log.
#
# USER ORDER 09-11 ~19:25 "no hold, get everything into main asap" adds two modes:
#   NM_UNVERIFIED=1  land NEW GroupApproximation .lean files (not on origin/main) WITHOUT a green
#                    probe record; they are not wired into the root, so the root build stays green.
#                    An edit to a module that already exists on origin/main is refused in this mode.
#   NM_ATTIC=1       preserve any files (typically red edits to existing modules) on main as text
#                    copies under attic/inflight/<lane>/<path>.txt; the real module is unchanged.
set -uo pipefail
NM=/private/tmp/claude-501/-Users-user-nonsofic-existence/77122910-de5a-4e59-a488-7cea550292c5/scratchpad/nm
REPO=/Users/user/nonsofic_existence
LANE=${1:?usage: nmland.sh <lane> <msgfile> <path...>}; MSG=${2:?msgfile}; shift 2
[ $# -ge 1 ] || { echo "usage: nmland.sh <lane> <msgfile> <path...>"; exit 2; }
[ -s "$MSG" ] || { echo "REFUSED: empty message file $MSG"; exit 2; }
cd "$REPO" || exit 2
if [ -n "${NM_ATTIC:-}" ]; then
  git fetch -q origin main || exit 1
  for p in "$@"; do [ -f "$p" ] || { echo "REFUSED: missing $p"; exit 2; }; done
  MSGF=$(mktemp "$NM/msgs/land.XXXXXX"); cat "$MSG" > "$MSGF"
  printf '\nIn-flight copies preserved under attic/inflight/%s/ (text, never compiled); the modules on main are unchanged until their edits pass a probe.\n' "$LANE" >> "$MSGF"
  grep -q '^Claude-Session:' "$MSGF" || printf '\nCo-Authored-By: Claude Code <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01AbNSg2jtc4hbgUd6TerqSa\n' >> "$MSGF"
  ACI=(); WANTL=""
  for p in "$@"; do
    d="attic/inflight/$LANE/$p.txt"; BLOB=$(git hash-object -w "$p") || exit 1
    ACI+=("100644,$BLOB,$d"); WANTL="$WANTL$d"$'\n'
  done
  for attempt in $(seq 1 40); do
    for f in 1 2 3 4 5; do git fetch -q origin main 2>/dev/null && break; sleep 1; done
    BASE=$(git rev-parse refs/remotes/origin/main)
    IDX=$(mktemp "$NM/msgs/idx.XXXXXX"); rm -f "$IDX"; export GIT_INDEX_FILE="$IDX"
    git read-tree "$BASE" || { unset GIT_INDEX_FILE; exit 1; }
    for ci in "${ACI[@]}"; do git update-index --add --cacheinfo "$ci" || exit 1; done
    TREE=$(git write-tree); unset GIT_INDEX_FILE; rm -f "$IDX"
    [ "$TREE" = "$(git rev-parse "${BASE}^{tree}")" ] && { echo "NOTHING TO LAND (attic copies identical)"; exit 0; }
    NEW=$(git commit-tree "$TREE" -p "$BASE" -F "$MSGF") || exit 1
    EXTRA=$(comm -23 <(git diff --name-only "$BASE" "$NEW" | sort) <(printf '%s' "$WANTL" | sort))
    [ -z "$EXTRA" ] || { echo "REFUSED: unexpected paths: $EXTRA"; exit 2; }
    if git -c credential.helper= -c credential.helper='!f() { echo "username=SauersML"; echo "password=$(gh auth token -u SauersML)"; }; f' push -q origin "$NEW:refs/heads/main" 2>/dev/null; then
      echo "LANDED ATTIC $NEW:"; git show --stat --format= "$NEW" | tail -3
      echo "$(date '+%F %T') $LANE-attic $NEW $*" >> "$NM/landed.log"; rm -f "$MSGF"; exit 0
    fi
    sleep $(( (RANDOM % 3) + 1 ))
  done
  exit 1
fi
LEANS=()
for p in "$@"; do
  if [ "$p" = "GroupApproximation.lean" ] && [ -z "${NM_ALLOW_ROOT:-}" ]; then echo "REFUSED: lanes never land the root; the lead wires"; exit 2; fi
  [ -f "$p" ] || { echo "REFUSED: missing $p"; exit 2; }
  case "$p" in
    *.lean)
      # Comparator challenge files (Palomar/*Challenge.lean) carry the protocol's deliberate `sorry`
      # holes, exactly like the landed Palomar/LIXChallenge.lean; only there is `sorry` permitted.
      NM_HOLES=0; case "$p" in Palomar/*Challenge.lean) NM_HOLES=1;; esac
      if NM_HOLES=$NM_HOLES python3 - "$p" <<'PY'
import re,sys
src=open(sys.argv[1],encoding='utf-8').read()
out=[];i=0;depth=0;n=len(src)
while i<n:
    if src.startswith('/-',i): depth+=1;i+=2;continue
    if depth and src.startswith('-/',i): depth-=1;i+=2;continue
    if depth: i+=1;continue
    if src.startswith('--',i):
        j=src.find('\n',i); i=n if j<0 else j; continue
    if src[i]=='"':
        j=i+1
        while j<n and src[j]!='"':
            j+=2 if src[j]=='\\' else 1
        i=j+1; continue
    out.append(src[i]);i+=1
code=''.join(out)
import os
pat = r'^\s*axiom\s|native_decide|implemented_by' if os.environ.get('NM_HOLES') == '1' else r'(?<![\w.\'])(sorry|admit)(?![\w\'])|^\s*axiom\s|native_decide|implemented_by'
sys.exit(0 if re.search(pat,code,re.M) else 1)
PY
      then echo "REFUSED: lexical sorry/admit/axiom/native_decide/implemented_by in $p"; exit 2; fi
      case "$p" in GroupApproximation/*) LEANS+=("$p");; esac;;
  esac
done
REC=""
# USER ORDER 09-11 ~22:45 "commit and push after LITERALLY EVERY EDIT ... do not clobber other work or overwrite".
# Clobber guard: a path that exists on origin/main with DIFFERENT bytes may be replaced only if the last
# origin commit touching it is (a) this lane's own landing (landed.log), (b) an ancestor of the green probe's
# base (the probe built on top of it), or (c) an ancestor of NM_BASE (the origin sha the lane synced its copy
# from).  Otherwise someone else changed the file after this lane's copy was made: refuse.
clobber_ok() {
  local p=$1 lastc
  git cat-file -e "origin/main:$p" 2>/dev/null || return 0
  [ "$(git rev-parse "origin/main:$p")" = "$(git hash-object "$p")" ] && return 0
  lastc=$(git log -1 --format=%H refs/remotes/origin/main -- "$p")
  grep -qE " $LANE $lastc( |\$)" "$NM/landed.log" && return 0
  for b in ${REC_BASE:-} ${NM_BASE:-}; do git merge-base --is-ancestor "$lastc" "$b" 2>/dev/null && return 0; done
  echo "REFUSED (clobber guard): $p on origin/main was last changed by $(git log -1 --format='%h %an: %s' "$lastc"), which is not your landing and not in your copy's base. Merge that change into your copy (git show origin/main:$p), then land with NM_BASE=<current origin sha>."
  return 1
}
root_closure_has() {   # is module path $1 reachable from GroupApproximation.lean at origin/main?
  git grep -n -E '^import GroupApproximation(\.[A-Za-z0-9_]+)+' refs/remotes/origin/main -- GroupApproximation GroupApproximation.lean 2>/dev/null \
    | python3 -c '
import sys,collections
g=collections.defaultdict(list)
for line in sys.stdin:
    parts=line.split(":",3)
    if len(parts)<4: continue
    f=parts[1]; mod=parts[3].split()[1]
    g[f[:-5].replace("/",".")].append(mod)
seen={"GroupApproximation"}; st=["GroupApproximation"]
while st:
    m=st.pop()
    for d in g.get(m,[]):
        if d not in seen: seen.add(d); st.append(d)
sys.exit(0 if sys.argv[1] in seen else 1)' "$(echo "${1%.lean}" | tr / .)"
}
if [ -n "${NM_UNVERIFIED:-}" ]; then
  git fetch -q origin main || exit 1
  for p in ${LEANS[@]+"${LEANS[@]}"}; do
    if git cat-file -e "origin/main:$p" 2>/dev/null; then
      # Re-landing your OWN unverified file after an edit is allowed when it is not reachable from the root.
      if root_closure_has "$p"; then
        echo "REFUSED (NM_UNVERIFIED): $p is reachable from the root on origin/main; an unverified edit would red the root. Preserve it with NM_ATTIC=1, land it for real after a green probe."; exit 2
      fi
      clobber_ok "$p" || exit 2
    fi
  done
  printf '\nUnverified: these new modules have not yet passed a probe and are not wired into the root import list (user order: everything on main at once).\n' >> "$MSG.unverified"
elif [ ${#LEANS[@]} -gt 0 ] && [ -z "${NM_ALLOW_ROOT:-}" ]; then
  for r in $(ls -t "$NM/lanes/$LANE".green.* 2>/dev/null); do
    ok=1
    for p in ${LEANS[@]+"${LEANS[@]}"}; do h=$(md5 -q "$p"); grep -qxF "$h  $p" "$r" || { ok=0; break; }; done
    [ $ok -eq 1 ] && { REC=$r; break; }
  done
  [ -n "$REC" ] || { echo "REFUSED: no green probe record of lane $LANE holds the CURRENT bytes of every landed .lean (edited after the green probe? re-probe first)"; exit 2; }
  echo "evidence: $REC"
  REC_BASE=$(sed -n 's/^# base //p' "$REC" | head -1)
fi
git fetch -q origin main || exit 1
if [ -z "${NM_UNVERIFIED:-}" ]; then
  for p in "$@"; do clobber_ok "$p" || exit 2; done
fi
for p in ${LEANS[@]+"${LEANS[@]}"}; do
  for imp in $(grep -E '^import GroupApproximation(\.[A-Za-z0-9_]+)+[[:space:]]*$' "$p" | awk '{print $2}'); do
    ip="${imp//.//}.lean"
    inthis=0; for q in "$@"; do [ "$q" = "$ip" ] && inthis=1; done
    [ $inthis -eq 1 ] && continue
    git cat-file -e "origin/main:$ip" 2>/dev/null || { echo "REFUSED: $p imports $imp, which is not on origin/main and not in this landing"; exit 2; }
    if [ -n "$REC" ] && grep -qE "  $ip\$" "$REC"; then
      oh=$(git show "origin/main:$ip" | md5 -q); rh=$(grep -E "  $ip\$" "$REC" | awk '{print $1}')
      [ "$oh" = "$rh" ] || { echo "REFUSED: $p was built against an EDITED $ip that differs from origin/main; land that file in the same call"; exit 2; }
    fi
  done
done
MSGF=$(mktemp "$NM/msgs/land.XXXXXX")
cat "$MSG" > "$MSGF"
[ -f "$MSG.unverified" ] && { cat "$MSG.unverified" >> "$MSGF"; rm -f "$MSG.unverified"; }
grep -q '^Claude-Session:' "$MSGF" || printf '\nCo-Authored-By: Claude Code <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01AbNSg2jtc4hbgUd6TerqSa\n' >> "$MSGF"
# Blobs once (content-addressed); the retry loop only rebuilds the tree on the newest tip.  Many lanes push
# concurrently, so retry up to 40 times with jitter, and retry a fetch that loses the ref lock to a peer's fetch.
CACHEINFO=()
for p in "$@"; do
  BLOB=$(git hash-object -w "$p") || exit 1
  MODE=100644; [ -x "$p" ] && MODE=100755
  CACHEINFO+=("$MODE,$BLOB,$p")
done
for attempt in $(seq 1 40); do
  for f in 1 2 3 4 5; do git fetch -q origin main 2>/dev/null && break; sleep 1; done
  BASE=$(git rev-parse refs/remotes/origin/main)
  IDX=$(mktemp "$NM/msgs/idx.XXXXXX"); rm -f "$IDX"
  export GIT_INDEX_FILE="$IDX"
  git read-tree "$BASE" || { unset GIT_INDEX_FILE; exit 1; }
  for ci in "${CACHEINFO[@]}"; do git update-index --add --cacheinfo "$ci" || exit 1; done
  TREE=$(git write-tree)
  unset GIT_INDEX_FILE; rm -f "$IDX"
  if [ "$TREE" = "$(git rev-parse "${BASE}^{tree}")" ]; then echo "NOTHING TO LAND: paths identical to origin/main ($(git rev-parse --short "$BASE"))"; exit 0; fi
  NEW=$(git commit-tree "$TREE" -p "$BASE" -F "$MSGF") || exit 1
  CHANGED=$(git diff --name-only "$BASE" "$NEW" | sort)
  WANT=$(printf '%s\n' "$@" | sort)
  EXTRA=$(comm -23 <(echo "$CHANGED") <(echo "$WANT"))
  [ -z "$EXTRA" ] || { echo "REFUSED: commit would touch unexpected paths:"; echo "$EXTRA"; exit 2; }
  ERRF=$(mktemp "$NM/msgs/push.XXXXXX")
  if git -c credential.helper= -c credential.helper='!f() { echo "username=SauersML"; echo "password=$(gh auth token -u SauersML)"; }; f' \
       push -q origin "$NEW:refs/heads/main" 2>"$ERRF"; then
    echo "LANDED $NEW on origin/main (parent $(git rev-parse --short "$BASE")):"
    git show --stat --format= "$NEW" | tail -n +1
    echo "$(date '+%F %T') $LANE $NEW $*" >> "$NM/landed.log"
    rm -f "$ERRF" "$MSGF"
    exit 0
  fi
  if grep -qE 'Permission|403|denied' "$ERRF"; then cat "$ERRF"; exit 1; fi
  grep -q 'non-fast-forward\|fetch first\|cannot lock ref' "$ERRF" || echo "push failed (attempt $attempt): $(head -c 400 "$ERRF" | tr '\n' ' ')"
  rm -f "$ERRF"; sleep $(( (RANDOM % 3) + 1 ))
done
echo "FAILED to land after 40 attempts"; exit 1
