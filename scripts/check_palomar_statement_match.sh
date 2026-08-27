#!/usr/bin/env bash
# Compare the compared theorem as ELABORATED in the two Palomar modules.
#
# WHY THIS EXISTS.  `leanprover/comparator` decides a submission by exporting
# both modules and comparing the configured theorem's `ConstantVal`
# STRUCTURALLY -- not up to definitional unfolding -- and then walking every
# constant that type mentions, requiring each to be identical in both
# environments (`Comparator/Compare.lean`, and the declaration-closure note in
# PalomarSubmission/docs).  Nothing else in this repository looks at that.
# `scripts/check_palomar_shared_block.py` compares the two files as TEXT, which
# catches drift in the definition block and in the signature; it cannot catch a
# difference that only appears after elaboration -- a different instance
# resolved on one side, a coercion inserted on one side, an `open` that changes
# what a name means.  Those compile cleanly on both sides and fail at the
# registry, after the commit is public.
#
# WHAT IT COMPARES.  Each driver prints the declaration's level parameters, the
# structural hash of its type, the sorted list of constants the type mentions,
# and the type itself with `pp.all`.  Identical output on both sides is the
# local statement of the same fact Comparator checks.
#
# It needs a built environment, so it runs after `lake build`, not in the
# source scan.
set -uo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

work=$(mktemp -d "${TMPDIR:-/tmp}/palomar-stmt.XXXXXX") || exit 1
trap 'rm -rf "$work"' EXIT

for side in Challenge Solution; do
  driver="scripts/Palomar${side}Type.lean"
  if [ ! -f "$driver" ]; then
    echo "::error::[palomar] $driver is missing; the statement match cannot be checked"
    exit 1
  fi
  if ! lake env lean "$driver" > "$work/$side.raw" 2> "$work/$side.err"; then
    echo "::error::[palomar] $driver failed to run"
    sed -n '1,20p' "$work/$side.err"
    exit 1
  fi
  # Drop everything before the report so a `sorry` warning on the challenge
  # side cannot masquerade as a difference.
  sed -n '/^declaration:/,$p' "$work/$side.raw" > "$work/$side.txt"
  if [ ! -s "$work/$side.txt" ]; then
    echo "::error::[palomar] $driver produced no report; it did not find the declaration"
    sed -n '1,20p' "$work/$side.raw"
    exit 1
  fi
done

if ! diff -u "$work/Challenge.txt" "$work/Solution.txt" > "$work/diff"; then
  echo "::error::[palomar] the compared statement differs between Palomar.Challenge and PalomarSolution after elaboration"
  sed -n '1,40p' "$work/diff"
  exit 1
fi

echo "palomar: challenge and solution elaborate the compared statement identically"
sed -n '1,4p' "$work/Challenge.txt"
