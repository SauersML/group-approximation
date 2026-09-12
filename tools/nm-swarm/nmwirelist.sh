#!/usr/bin/env bash
# nmwirelist.sh   (LEAD)  -- list landed campaign .lean modules not yet reachable from the root.
# Reads $NM/landed.log, keeps GroupApproximation/**/*.lean paths that are on origin/main now,
# and prints the module names that are neither imported by origin/main's root nor imported by
# another listed module (so wiring the printed names reaches every landed module).
set -uo pipefail
NM=/private/tmp/claude-501/-Users-user-nonsofic-existence/77122910-de5a-4e59-a488-7cea550292c5/scratchpad/nm
cd /Users/user/nonsofic_existence || exit 2
git fetch -q origin main
[ -s "$NM/landed.log" ] || { echo "(no landings)"; exit 0; }
ROOT=$(git show origin/main:GroupApproximation.lean | grep '^import GroupApproximation' | awk '{print $2}' | sort -u)
PATHS=$(awk '{for (i=4;i<=NF;i++) print $i}' "$NM/landed.log" | grep -E '^GroupApproximation/.*\.lean$' | sort -u)
MODS=""
for p in $PATHS; do
  git cat-file -e "origin/main:$p" 2>/dev/null || continue
  m=${p%.lean}; m=${m//\//.}
  printf '%s\n' "$ROOT" | grep -qxF "$m" && continue
  MODS="$MODS $m"
done
# drop modules imported by another unwired landed module
OUT=""
for m in $MODS; do
  imported=0
  for q in $MODS; do
    [ "$q" = "$m" ] && continue
    qp="${q//.//}.lean"
    git show "origin/main:$qp" | grep -qxE "import $m[[:space:]]*" && { imported=1; break; }
  done
  [ $imported -eq 0 ] && OUT="$OUT $m"
done
echo "unwired landed modules (tops):$OUT"
