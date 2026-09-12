#!/usr/bin/env bash
# q-targets.sh (runs ON MSI, read-only): resolve the mirror tip, check its root files, and list the campaign base
# targets at it: landed BowenChapman / Dynamics / campaign KunThom, Kazhdan and Sofic modules, plus every
# GroupApproximation module imported by a wip/bowen-chapman snapshot that exists at the tip, plus the Palomar libs.
set -u
P=/projects/standard/__MSI_GROUP__/__MSI_USER__; M=$P/nm/mirror.git; W=$P/bc/qt.$$
( flock -w 600 8 && git -C "$M" fetch -q origin ) 8>"$P/nm/mirror.lock" || echo FETCH_FAILED
T=$(git -C "$M" rev-parse refs/heads/main)
git -C "$M" ls-tree -r --name-only "$T" > "$W.all" || { echo LSTREE_FAILED; echo SENTINEL=1; exit 0; }
echo "tip=$T files=$(wc -l < "$W.all")"
for r in GroupApproximation.lean lake-manifest.json lakefile.toml; do
  grep -qxF "$r" "$W.all" && echo "present $r" || echo "ABSENT $r"
done
grep -E '^wip/bowen-chapman/.*\.lean$' "$W.all" | while IFS= read -r f; do git -C "$M" show "$T:$f"; done \
  | sed -n 's/^import \(GroupApproximation\.[A-Za-z0-9_.]*\).*/\1/p' | LC_ALL=C sort -u | tr . / | sed 's/$/.lean/' > "$W.imp"
{
  grep -E '^GroupApproximation/(BowenChapman|Dynamics)/.*\.lean$' "$W.all"
  grep -E '^GroupApproximation/KunThom/(CentralizerNormalization|NormalizationFromCriterion|FixedPointNormalization|ComponentCountingNormalization)[^/]*\.lean$' "$W.all"
  grep -E '^GroupApproximation/(Kazhdan/SemidirectProductKazhdan|Sofic/WreathCentralizerNormalization)[^/]*\.lean$' "$W.all"
  [ -s "$W.imp" ] && grep -xFf "$W.imp" "$W.all"
} | LC_ALL=C sort -u | sed 's/\.lean$//' | tr / . > "$W.targets"
for lib in BowenChapmanChallenge BowenChapmanSolution; do
  if grep -qxF "Palomar/$lib.lean" "$W.all" && git -C "$M" show "$T:lakefile.toml" | grep -qF "\"Palomar.$lib\""; then
    echo "Palomar.$lib" >> "$W.targets"
  fi
done
echo "wip_imports_resolved=$(grep -cxFf "$W.imp" "$W.all" 2>/dev/null || echo 0) of $(wc -l < "$W.imp")"
grep -vxFf "$W.all" "$W.imp" | sed 's/^/unresolved_import /' | head -10
echo "targets=$(wc -l < "$W.targets")"
tr '\n' ' ' < "$W.targets"; echo
cp "$W.targets" "$P/bc/base-targets.txt"; echo "$T" > "$P/bc/base-targets.sha"
rm -f "$W.all" "$W.imp" "$W.targets"
echo SENTINEL=0
