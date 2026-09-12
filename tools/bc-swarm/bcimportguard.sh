#!/usr/bin/env bash
# bcimportguard.sh <base-commit> <new-commit-or-tree>      (read-only; run it at commit-tree time, before pushing)
# Refuses (exit 1) when the change BASE -> NEW deletes a Lean module under GroupApproximation/ or Palomar/ that some
# .lean file in the NEW tree still imports, and names every importer as path:line:text. The NEW tree is the one
# being committed, so an importer landed by another lane after your base is caught once you rebuild on its tip.
# Import lines are matched as Lean writes them: optional `public`/`private`/`meta` prefixes, several modules on one
# line, trailing whitespace; a module name inside a `--` comment is not an import.
# Exit 0: no deleted module is still imported. Exit 1: refusal. Exit 2: the guard could not read its input (a guard
# that cannot read must fail, not pass).
# BC_REPO overrides the repository (default: the shared checkout).
set -uo pipefail
REPO=${BC_REPO:-/Users/user/nonsofic_existence}
unreadable() { echo "IMPORT GUARD FAILED: $1"; exit 2; }
BASE=${1:-}; NEW=${2:-}
{ [ -n "$BASE" ] && [ -n "$NEW" ]; } || unreadable "usage: bcimportguard.sh <base-commit> <new-commit-or-tree>"
cd "$REPO" || unreadable "no repo at $REPO"
git cat-file -e "$BASE^{commit}" 2>/dev/null || unreadable "base ${BASE:0:9} is not a local commit"
git cat-file -e "$NEW^{tree}" 2>/dev/null || unreadable "new ${NEW:0:9} is not a local commit or tree"
if git cat-file -e "$NEW:GroupApproximation.lean" 2>/dev/null; then
  git grep -q -E -e '^import ' "$NEW" -- GroupApproximation.lean \
    || unreadable "positive control: git grep finds no import line in GroupApproximation.lean of ${NEW:0:9}"
fi
DELETED=$(git diff --no-renames --name-only --diff-filter=D "$BASE" "$NEW") || unreadable "git diff ${BASE:0:9} ${NEW:0:9}"
refused=0; checked=0
while IFS= read -r p; do
  [ -n "$p" ] || continue
  case "$p" in GroupApproximation/*.lean|Palomar/*.lean) ;; *) continue;; esac
  mod=${p%.lean}; mod=${mod//\//.}; esc=${mod//./\\.}
  pat="^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+([^-]*[[:space:]])?${esc}([[:space:]]|$)"
  checked=$((checked+1))
  hits=$(git grep -n -I -E -e "$pat" "$NEW" -- '*.lean'); rc=$?
  [ $rc -le 1 ] || unreadable "git grep for importers of $mod exited $rc"
  if [ $rc -eq 0 ]; then
    refused=1
    echo "deleted $mod is still imported in ${NEW:0:9}:"
    printf '%s\n' "$hits" | sed -e "s|^$NEW:|  |" | head -20
  fi
done <<< "$DELETED"
if [ $refused -eq 1 ]; then
  echo "IMPORT GUARD REFUSED: remove or retarget those imports in the same commit, or keep the module"
  exit 1
fi
echo "IMPORT GUARD OK: $checked deleted Lean module(s), none imported by the new tree"
exit 0
