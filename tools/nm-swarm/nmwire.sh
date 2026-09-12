#!/usr/bin/env bash
# nmwire.sh [--targets "<Module...>"] <Module.Name> [...]        (LEAD ONLY)
#
# Wire landed orphan modules into GroupApproximation.lean, prove it with a ROOT build of
# origin/main@SHA + the wired root in the lead clone (SLURM, 32 cpus), and on ROOT GREEN
# land the root as CURRENT origin/main's root plus exactly the new import lines (inserted
# after the last import line, never after the closing docstring).  With no modules it is a
# plain root build of origin/main (base warm-up).
set -uo pipefail
NM=/private/tmp/claude-501/-Users-user-nonsofic-existence/77122910-de5a-4e59-a488-7cea550292c5/scratchpad/nm
REPO=/Users/user/nonsofic_existence
MSI=/Users/user/msi-node/msi; SOCK=/tmp/msi-login.sock; ALIAS=__MSI_LOGIN__
P=/projects/standard/__MSI_GROUP__/__MSI_USER__
CLONE=$P/cc_clones/lead
TARGETS=""
if [ "${1:-}" = "--targets" ]; then TARGETS=$2; shift 2; fi
MODS="$*"
TAG=$(date +%m%d-%H%M%S)-$$
cd "$REPO" || exit 2
git fetch -q origin main || exit 1
SHA=$(git rev-parse origin/main)
for m in $MODS; do
  p="${m//.//}.lean"
  git cat-file -e "$SHA:$p" 2>/dev/null || { echo "REFUSED: $m is not on origin/main"; exit 2; }
done
sed -e "s|__CLONE__|$CLONE|" -e "s|__TAG__|$TAG|" -e "s|__SHA__|$SHA|" -e "s|__MODS__|$MODS|" -e "s|__TARGETS__|$TARGETS|" "$NM/remote/wirejob.template.sh" > "$NM/msgs/wirejob-$TAG.sh"
RSH="ssh -S $SOCK -o HostKeyAlias=$ALIAS -o LogLevel=ERROR"
"$MSI" true >/dev/null 2>&1 || "$MSI" up >/dev/null 2>&1 || exit 4
"$MSI" "mkdir -p $CLONE/.nm" >/dev/null 2>&1
rsync -lc -e "$RSH" "$NM/msgs/wirejob-$TAG.sh" "$ALIAS:$CLONE/.nm/wirejob-$TAG.sh" || exit 4
echo "root build tag=$TAG base=${SHA:0:9} wire: ${MODS:-<none>}"
OUT=$("$MSI" "bash $P/nm/dispatch.sh $CLONE/.nm/wirejob-$TAG.sh $CLONE/.nm/rootout-$TAG.txt nm-root 32" 2>&1); RC=$?
printf '%s\n' "$OUT"
printf '%s\n' "$OUT" | grep -q '^ROOT GREEN' || { echo "not landing the root (rc=$RC)"; exit 1; }
[ -n "$MODS" ] || { echo "base root build green at ${SHA:0:9}"; exit 0; }
NEWLINES=$(printf '%s\n' "$OUT" | sed -n '/^--- wired lines/,/^ROOT GREEN/p' | grep '^import GroupApproximation')
[ -n "$NEWLINES" ] || { echo "no import lines to add (already wired?)"; exit 0; }
git fetch -q origin main
git show origin/main:GroupApproximation.lean > "$NM/msgs/root-$TAG.cur"
printf '%s\n' "$NEWLINES" > "$NM/msgs/root-$TAG.add"
python3 - "$NM/msgs/root-$TAG.cur" "$NM/msgs/root-$TAG.add" "$REPO/GroupApproximation.lean.nmwire" <<'PY'
import sys
cur=open(sys.argv[1]).read().split('\n'); add=[l.strip() for l in open(sys.argv[2]) if l.strip()]
have={l.strip() for l in cur if l.startswith('import ')}
add=[l for l in add if l not in have]
last=max(i for i,l in enumerate(cur) if l.startswith('import '))
new=cur[:last+1]+add+cur[last+1:]
first_prose=next((i for i,l in enumerate(new) if l.strip() and not l.startswith('import ') and not l.startswith('--')), len(new))
assert all(not l.startswith('import ') for l in new[first_prose:]), 'import after prose'
open(sys.argv[3],'w').write('\n'.join(new))
print(f'inserted {len(add)} import lines after line {last+1}')
PY
[ $? -eq 0 ] || { echo "root rebuild script failed"; exit 1; }
cat > "$NM/msgs/wire-$TAG.msg" <<EOF
Wire $(printf '%s\n' "$NEWLINES" | wc -l | tr -d ' ') landed non-MF campaign module(s) into the root

$(printf '%s\n' "$NEWLINES")

Root build of origin/main ${SHA:0:9} plus these imports is green in the lead clone
(log .nm/root-$TAG.log).
EOF
# land the root from a private copy (never the shared working tree's root)
TMPD=$(mktemp -d "$NM/msgs/wire.XXXXXX")
mkdir -p "$TMPD/GroupApproximation"
cp "$REPO/GroupApproximation.lean.nmwire" "$TMPD/GroupApproximation.lean"; rm -f "$REPO/GroupApproximation.lean.nmwire"
BASE=$(git rev-parse origin/main)
IDX=$(mktemp "$NM/msgs/idx.XXXXXX"); rm -f "$IDX"
for attempt in 1 2 3 4 5 6; do
  git fetch -q origin main; BASE=$(git rev-parse origin/main)
  git show "$BASE:GroupApproximation.lean" > "$NM/msgs/root-$TAG.cur2"
  python3 - "$NM/msgs/root-$TAG.cur2" "$NM/msgs/root-$TAG.add" "$TMPD/GroupApproximation.lean" <<'PY'
import sys
cur=open(sys.argv[1]).read().split('\n'); add=[l.strip() for l in open(sys.argv[2]) if l.strip()]
have={l.strip() for l in cur if l.startswith('import ')}
add=[l for l in add if l not in have]
last=max(i for i,l in enumerate(cur) if l.startswith('import '))
open(sys.argv[3],'w').write('\n'.join(cur[:last+1]+add+cur[last+1:]))
PY
  BLOB=$(git hash-object -w "$TMPD/GroupApproximation.lean")
  export GIT_INDEX_FILE="$IDX"; git read-tree "$BASE"; git update-index --add --cacheinfo "100644,$BLOB,GroupApproximation.lean"; TREE=$(git write-tree); unset GIT_INDEX_FILE; rm -f "$IDX"
  [ "$TREE" = "$(git rev-parse "$BASE^{tree}")" ] && { echo "root already has these imports"; exit 0; }
  printf '\nCo-Authored-By: Claude Code <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01AbNSg2jtc4hbgUd6TerqSa\n' >> "$NM/msgs/wire-$TAG.msg"
  NEW=$(git commit-tree "$TREE" -p "$BASE" -F "$NM/msgs/wire-$TAG.msg")
  [ "$(git diff --name-only "$BASE" "$NEW")" = "GroupApproximation.lean" ] || { echo "REFUSED: unexpected paths"; exit 2; }
  if git -c credential.helper= -c credential.helper='!f() { echo "username=SauersML"; echo "password=$(gh auth token -u SauersML)"; }; f' push -q origin "$NEW:refs/heads/main" 2>/dev/null; then
    echo "LANDED ROOT $NEW"; git diff "$BASE" "$NEW" | grep '^[+-]import'
    echo "$(date '+%F %T') lead-wire $NEW $MODS" >> "$NM/landed.log"; exit 0
  fi
  echo "push race $attempt"; sleep $((attempt*2))
done
exit 1
