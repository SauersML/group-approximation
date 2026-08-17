---
rg: 2
id: leavitt-corner-one-sided-lift-exists
kind: claim
title: A one-sided invertible pair in the Leavitt corner whose defect survives evaluation
distinct_from:
  leavitt-corner-idempotent-unital-surjection: that is the established construction of the corner and its unital surjection; this is the open lifting problem stated inside that corner, and is exactly what the construction does not supply.
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that is the same search run in the whole algebra with the right factor pinned over s_0, which is what the cellular-automaton reading needs; this one runs inside the corner e A e against the corner identity e and pins nothing over pi, so the two have different unknowns, different necessary conditions, and neither implies the other.
  leavitt-rank-three-lift-inverse-support-thirteen: that is a support bound for a factor of the rank-three lift in the whole group algebra; this asks for a pair inside the corner, where the identity is e and the support bound is not known to apply.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

With `A = F_2[R^x]`, `e = [g] + [g^2]` and `pi_e : eAe ->> R` as in
`leavitt-corner-idempotent-unital-surjection`: exhibit `a, b` in `eAe` with

    a b = e        and        pi_e(b a) != 1_R.

**This is the missing theorem of the whole lane.**  It is not a
reformulation of "Kaplansky is false" — it is a specific, finite-looking
identity in one explicitly presented corner, and by
`leavitt-unit-group-algebra-not-directly-finite` it would refute the
conjecture.  The second condition is what makes it usable: `ba != e` alone
would already do, but `pi_e(ba) != 1` is the version one can *check*, since
`pi_e` is evaluation and lands in a ring where the Leavitt normal form
decides equality.

## Why the corner rather than the algebra

Not convenience, though the argument has to be stated carefully.  As recorded
in `leavitt-corner-idempotent-unital-surjection`, the `F_2`-augmentation kills
any hope of realizing the full **Leavitt relations** in `F_2[G]` itself, or in
any corner `fAf` with `eps(f) = 1`.  The corner at `e` has `eps(e) = 0`, so
that obstruction is inactive there — this is the first place in the
construction where the standard two-line no-go stops applying, and it is why
the family route `binary-leavitt-family-lifts-into-unit-corner` has to be
stated here and nowhere more comfortable.

The augmentation does *not* forbid a bare pair with `ab = 1 != ba` in the
whole of `A`; applying `eps` there yields only `eps(a) = eps(b) = 1`.  So this
claim is a corner statement by construction, not by necessity: it is where the
available material points, and a pair found directly in `A` would serve the
same purpose.

## What is known against it

Nothing decisive.  The nearest constraint is
`leavitt-rank-three-lift-inverse-support-thirteen`, which excludes the
smallest completions of the explicit rank-three generator lift in the *whole*
algebra; transporting that floor into the corner is not done and is not
routine, since the corner's identity `e` has support two and its elements are
not free to have arbitrary support patterns.

Two strictly stronger targets that would settle this, in decreasing order of
ambition, are `binary-leavitt-family-lifts-into-unit-corner` (lift the whole
family, equivalently split `pi_e` by a unital ring section) and — bypassing
this claim entirely, via a different route into the same conclusion —
`leavitt-corner-kernel-is-jacobson-radical`.
