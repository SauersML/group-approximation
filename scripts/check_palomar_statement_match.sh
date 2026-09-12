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
# WHY SEVERAL PAIRS.  A submission is exactly one Comparator configuration, and
# this repository offers three -- `Palomar/comparator.json`,
# `Palomar/comparator-lix.json` and `Palomar/comparator-lix-strong.json` -- so
# it is submitted once per configuration and each pair has to match on its own.
# The loops below are over the driver prefixes, empty for the non-MF pair,
# `LIX` for the LIX pair and `LIXStrong` for the strengthened one, matching the
# names in `PALOMAR_CONFIGS` and `PALOMAR_PENDING_CONFIGS` in
# `scripts/check_palomar_submission.py`.  Every pair is run even after one
# fails: knowing that both differ is different information from knowing that
# one does, and a script that stopped at the first would need a second
# invocation to find out.
#
# WHY THE THIRD PAIR IS DIFFERENT.  `Palomar/LIXStrongSolution.lean` proves each
# selected statement from one proposition the construction still owes, so its
# theorems carry a hypothesis the challenge's do not and are named `<theorem>_of`.
# Their statements therefore CANNOT match yet, and diffing them would report,
# every run, a difference that is the honest state of the work.
#
# What can be compared, and is the defect this repository actually hit on
# 2026-09-10, is the SHARED BLOCK: `cornerDiag` and `IsK1Injective`, written
# byte-identically in both files and elaborating to different terms because the
# solution's environment reaches a Mathlib instance the challenge's does not.
# `cornerDiag` is in the compared closure of all three theorems, so a difference
# there is a real Comparator failure.  The strengthened drivers therefore print
# the shared block first, then a line reading `pending-boundary:`, then the
# statements; this script diffs everything up to the boundary and GATES on it,
# and prints the rest for inspection without gating.
#
# The distinction is between a diff that cannot hold yet and a driver that did
# not run.  A driver that is missing, fails, or produces no report is an ERROR
# for the pending pair exactly as for the other two: a check that could not read
# its input must not read like a check that passed.
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

# The pending pairs.  The drivers must run and must produce a report -- that is
# gated -- and the part of the report before `pending-boundary:` must match.
# The part after it is printed and not gated, because the solution's theorems
# still carry the outstanding hypothesis.
for prefix in LIXStrong BowenChapman; do
  label="$prefix"
  pair_ok=1

  for side in Challenge Solution; do
    driver="scripts/Palomar${prefix}${side}Type.lean"
    out="$work/$label.$side"
    if [ ! -f "$driver" ]; then
      echo "::error::[palomar] $driver is missing; the $label shared-block match cannot be checked"
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
    sed -n '/^declaration:/,$p' "$out.raw" > "$out.txt"
    if [ ! -s "$out.txt" ]; then
      echo "::error::[palomar] $driver produced no report; it did not find the declaration"
      sed -n '1,20p' "$out.raw"
      pair_ok=0
      status=1
      continue
    fi
    # Everything strictly before the FIRST boundary line.
    #
    # `awk ... exit` and not `sed -n '/a/,/b/p'`: a sed range RESTARTS at the
    # next match of its opening address once the closing one has fired, so with
    # several `declaration:` sections a sed range would silently readmit every
    # section after the boundary -- which is the whole set this loop must not
    # gate on.  Caught by testing the extraction on a synthetic report before
    # trusting it.
    #
    # A report with no boundary at all is a driver that is not the one this
    # loop expects, and it must fail rather than be treated as all-shared: that
    # reading would gate on the statements and report a difference that is the
    # expected state of the work.  awk exits 3 in that case.
    if ! awk '/^pending-boundary:/ { found = 1; exit }
              { print }
              END { if (!found) exit 3 }' "$out.txt" > "$out.shared"; then
      echo "::error::[palomar] $driver printed no \`pending-boundary:\` line; it is not the driver this check expects"
      pair_ok=0
      status=1
      continue
    fi
    if [ ! -s "$out.shared" ]; then
      echo "::error::[palomar] $driver printed no shared-block section before pending-boundary:"
      pair_ok=0
      status=1
    fi
  done

  if [ "$pair_ok" -ne 1 ]; then
    continue
  fi

  if ! diff -u "$work/$label.Challenge.shared" "$work/$label.Solution.shared" \
       > "$work/$label.shared.diff"; then
    echo "::error::[palomar] the shared block differs between Palomar.${prefix}Challenge and Palomar.${prefix}Solution after elaboration"
    sed -n '1,40p' "$work/$label.shared.diff"
    status=1
    continue
  fi

  echo "palomar: the $label challenge and solution elaborate the shared block identically"
  grep -c '^declaration:' "$work/$label.Challenge.shared" \
    | sed 's/^/palomar: compared shared-block declarations: /'
  grep '^declaration:' "$work/$label.Challenge.shared" | sed 's/^/palomar:   /'
  echo "palomar: $label is PENDING -- its solution proves each selected statement from an"
  echo "palomar: outstanding proposition, so the statements below are reported, not gated."
  grep '^declaration:' "$work/$label.Challenge.txt" | sed 's/^/palomar:   challenge /'
  grep '^declaration:' "$work/$label.Solution.txt" | sed 's/^/palomar:   solution  /'
done

exit "$status"
