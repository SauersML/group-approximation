#!/usr/bin/env bash
# Block a push that ADDS a source-scan finding, before it can reach main.
#
# WHY THIS EXISTS.  `scripts/check.py` is the same scan the prover's "Build and
# audit" job runs, and a finding there fails its zero-tolerance step in about
# six minutes.  `verified` then stops advancing until someone lands a fix.  On
# 2026-08-18 that cost roughly four and a half hours: 85989ae8 restored nineteen
# `set_option maxHeartbeats` bumps the scan bans, so every commit was red until
# c0f1e4e8 removed them.  The scan reads only sources, needs no build and takes
# five seconds, so the entire window was avoidable at push time.
#
# WHY PRE-PUSH AND NOT PRE-COMMIT.  Work reaches main here through the
# `GIT_INDEX_FILE` + `commit-tree` plumbing route, which runs no hooks at all.
# Pre-push is the only chokepoint every landing path crosses.
#
# WHY IT SCANS THE PUSHED TREE, NOT THE WORKING TREE.  The shared checkout
# always holds several lanes' half-finished files; a working-tree scan would
# block every lane on every other lane's scratch.
#
# WHAT IT CHECKS BEYOND check.py.  `scripts/check.py` finds a module that
# nothing imports (an orphan, never compiled, never audited).  It does NOT find
# the mirror defect: an IMPORT NAMING A MODULE THAT IS NOT IN THE TREE.  Verified
# by construction -- adding `import GroupApproximation.Analysis.ThisModuleDoesNotExist`
# to the root and rescanning produces no new finding.  That defect is worse than
# an orphan: it is a hard failure at the first import, so it does not merely stop
# certification, it breaks every lane's build at once.  It is also live as this
# lands -- the shared working tree's root module imports an UNTRACKED
# `Analysis/CStarTensorProductAlgebra`, one careless `git add -A` away from main.
# The two halves are one gate, so this scans for both.
#
# WHY IT COMPARES AGAINST A BASELINE RATHER THAN DEMANDING ZERO.  Absolute
# "must be clean" turns any pre-existing red into a total push freeze for every
# lane at once -- which is a worse outage than the red it guards, and it would
# also block the very push that fixes it if that push is not a complete repair.
# So the gate is a REGRESSION gate: it blocks findings your push introduces and
# stays out of the way of findings already on the remote.  A red main still gets
# fixed by whoever owns it; it just does not take six lanes down with it.
set -uo pipefail

sha="${1:?usage: prepush_source_scan.sh <commit-ish> [baseline-ish]}"
baseline="${2:-refs/remotes/origin/main}"

repo=$(git rev-parse --show-toplevel 2>/dev/null) || exit 0
[ -f "$repo/scripts/check.py" ] || exit 0

work=$(mktemp -d "${TMPDIR:-/tmp}/prepush-scan.XXXXXX") || exit 0
trap 'rm -rf "$work"' EXIT

# Every failure below is a hook problem, not a repository problem: fail OPEN,
# so a broken guard can never be what stops work from landing.
scan_tree() {  # <rev> <outfile> -> 0 scanned, 1 could not scan
  local rev="$1" out="$2" dir="$work/$3"
  mkdir -p "$dir" || return 1
  git archive --format=tar "$rev" 2>/dev/null | tar -x -C "$dir" 2>/dev/null || return 1
  [ -f "$dir/scripts/check.py" ] || return 1
  ( cd "$dir" && python3 scripts/check.py 2>&1 ) > "$out"
  local rc=$?
  # 0 = clean, 1 = findings; anything else is the scanner itself breaking.
  [ "$rc" -le 1 ] || return 1
  # The mirror check check.py does not do: a first-party import with no module.
  ( cd "$dir" && python3 - <<'MISSING' ) >> "$out" || return 1
import pathlib, re
root = pathlib.Path(".")
present = {"GroupApproximation"}
for f in root.rglob("*.lean"):
    if ".lake" in f.parts:
        continue
    present.add(str(f.with_suffix("")).replace("/", "."))
imp = re.compile(r"^\s*import\s+(GroupApproximation(?:\.[A-Za-z0-9_']+)*)\s*$")
for f in sorted(root.rglob("*.lean")):
    if ".lake" in f.parts:
        continue
    try:
        lines = f.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        continue
    for n, line in enumerate(lines, 1):
        m = imp.match(line)
        if m and m.group(1) not in present:
            print(f"::error::[missing import target] {f}:{n}: imports {m.group(1)}, "
                  f"which is not a module in this tree -- the build fails at this import")
MISSING
  return 0
}

if ! scan_tree "$sha" "$work/head.txt" head; then
  echo "prepush-scan: could not scan ${sha:0:8}; skipping (fail-open)" >&2
  exit 0
fi
grep -E '^::error::' "$work/head.txt" | sort -u > "$work/head.err"

if ! scan_tree "$baseline" "$work/base.txt" base; then
  echo "prepush-scan: could not scan the baseline; comparing against empty (fail-open)" >&2
  : > "$work/base.err"
else
  grep -E '^::error::' "$work/base.txt" | sort -u > "$work/base.err"
fi

new=$(comm -23 "$work/head.err" "$work/base.err")
carried=$(wc -l < "$work/base.err" | tr -d ' ')

if [ -z "$new" ]; then
  summary=$(sed -n 's/^source scan: //p' "$work/head.txt")
  echo "prepush-scan: no new source-scan findings at ${sha:0:8} ($summary)"
  [ "$carried" -gt 0 ] && echo "prepush-scan: note -- $carried finding(s) already on the remote, not introduced by you"
  exit 0
fi

echo "prepush-scan: BLOCKED -- this push introduces source-scan finding(s) that" >&2
echo "  the remote does not have.  This is the scan the prover's 'Build and audit'" >&2
echo "  job runs; landing it makes every certificate red and verified stops." >&2
printf '%s\n' "$new" | sed 's/^::error:://; s/^/  + /' >&2
[ "$carried" -gt 0 ] && echo "  ($carried pre-existing finding(s) ignored -- not yours)" >&2
echo "  bypass (only if you are certain): git push --no-verify" >&2
exit 1
