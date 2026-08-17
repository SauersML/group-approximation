---
rg: 2
id: leavitt-unit-algebra-not-directly-finite-by-radical-kernel
kind: route
title: A kernel inside the radical makes the quotient argument legal
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - leavitt-corner-idempotent-unital-surjection
  - leavitt-corner-kernel-is-jacobson-radical
  - binary-leavitt-algebra-not-directly-finite
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

**INVALIDATED 2026-08-17 by `leavitt-corner-kernel-not-jacobson-radical`.**
The second prerequisite is false: `ker(pi_e)` contains a nonzero idempotent,
and a Jacobson radical contains none.  The implication below is still valid —
nothing is wrong with the descent argument — but its hypothesis cannot be
supplied, so this route can never fire.

## Why sufficient

Direct finiteness descends modulo an ideal contained in the Jacobson radical
(proved in `direct-finiteness-quotient-failure-proof`): if `S` is directly
finite and `I subseteq J(S)`, then `S/I` is directly finite.

Apply this with `S = eAe` and `I = ker(pi_e)`, which lies in `J(eAe)` by the
second prerequisite.  If `eAe` were directly finite, so would be
`eAe / ker(pi_e) = R`, contradicting the third prerequisite.  Hence `eAe` is
not directly finite: there are `a, b` in `eAe` with `ab = e != ba`.

Pad as in `leavitt-unit-algebra-not-directly-finite-by-corner-padding`:
`alpha = a + (1-e)`, `beta = b + (1-e)` satisfy `alpha beta = 1` and
`beta alpha != 1` in `A`, all cross terms vanishing because `a, b` lie in the
corner.  So `A = F_2[R^x]` is not directly finite.

## Contrast with the other route

This one produces no witness.  It concludes from a structural hypothesis about
an ideal that a pair must exist, without saying which — the difference between
the two lanes is exactly the difference between a non-constructive descent
argument and an explicit lift.  It is also the reason the two are kept as
separate routes rather than merged: they fail for unrelated reasons and
succeed by unrelated means, and a graph that collapsed them would hide that a
computation of `J(e F_2[R^x] e)` is a distinct piece of work from a search for
`(a,b)`.
