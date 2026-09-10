#!/usr/bin/env bash
# Compare the compared theorems as ELABORATED in the Palomar modules.
#
# WHY THIS EXISTS.  `leanprover/comparator` decides a submission by exporting
# both modules and comparing the configured theorem's `ConstantVal`
# STRUCTURALLY -- not up to definitional unfolding -- and then walking every
# constant that type mentions, requiring each to be identical in both
# environments (`Comparator/Compare.lean`, and the declaration-closure note in
# PalomarSubmission/docs).  Nothing else in this repository looks at that.
# `scripts/check_palomar_submission.py` compares the two files as TEXT, which
# catches drift in the definition block and in the signature; it cannot catch a
# difference that only appears after elaboration -- a different instance
# resolved on one side, a coercion inserted on one side, an `open` that changes
# what a name means.  Those compile cleanly on both sides and fail at the
# registry, after the commit is public.
#
# WHAT IT COMPARES.  Each driver prints, for every theorem its configuration
# selects, the declaration's level parameters, the structural hash of its type,
# the sorted list of constants the type mentions, and the type itself with
# `pp.all`.  Identical output on both sides is the local statement of the same
# fact Comparator checks.
#
# WHY TWO PAIRS.  A submission is exactly one Comparator configuration, and
# this repository offers two -- `Palomar/comparator.json` and
# `Palomar/comparator-lix.json` -- so it is submitted twice and each pair has
# to match on its own.  The loop below is over the driver prefixes, empty for
# the non-MF pair and `LIX` for the LIX pair, matching the names in
# `PALOMAR_CONFIGS` in `scripts/check_palomar_submission.py`.  Every pair is
# run even after one fails: with two submissions, knowing that both differ is
# different information from knowing that one does, and a script that stopped
# at the first would need a second invocation to find out.
#
# It needs a built environment, so it runs after `lake build`, not in the
# source scan.
set -uo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

work=$(mktemp -d "${TMPDIR:-/tmp}/palomar-stmt.XXXXXX") || exit 1
trap 'rm -rf "$work"' EXIT

status=0

for prefix in "" LIX; do
  # A label for the messages: the empty prefix is the original non-MF pair.
  label="${prefix:-non-MF}"
  pair_ok=1

  for side in Challenge Solution; do
    driver="scripts/Palomar${prefix}${side}Type.lean"
    out="$work/$label.$side"
    if [ ! -f "$driver" ]; then
      echo "::error::[palomar] $driver is missing; the $label statement match cannot be checked"
      pair_ok=0
      status=1
      continue
    fi
    if ! lake env lean "$driver" > "$out.raw" 2> "$out.err"; then
      echo "::error::[palomar] $driver failed to run"
      sed -n '1,20p' "$out.err"
      pair_ok=0
      status=1
      continue
    fi
    # Drop everything before the first report so a `sorry` warning on the
    # challenge side cannot masquerade as a difference.  With several selected
    # theorems the drivers print one `declaration:` section each, in the order
    # the configuration lists them, and the whole run of sections is compared.
    sed -n '/^declaration:/,$p' "$out.raw" > "$out.txt"
    if [ ! -s "$out.txt" ]; then
      echo "::error::[palomar] $driver produced no report; it did not find the declaration"
      sed -n '1,20p' "$out.raw"
      pair_ok=0
      status=1
      continue
    fi
  done

  if [ "$pair_ok" -ne 1 ]; then
    continue
  fi

  if ! diff -u "$work/$label.Challenge.txt" "$work/$label.Solution.txt" > "$work/$label.diff"; then
    echo "::error::[palomar] the compared statement differs between Palomar.${prefix}Challenge and Palomar.${prefix}Solution after elaboration"
    sed -n '1,40p' "$work/$label.diff"
    status=1
    continue
  fi

  echo "palomar: the $label challenge and solution elaborate every compared statement identically"
  grep -c '^declaration:' "$work/$label.Challenge.txt" \
    | sed 's/^/palomar: compared declarations: /'
  grep '^declaration:' "$work/$label.Challenge.txt" | sed 's/^/palomar:   /'
done

exit "$status"
