---
rg: 2
id: stably-finite-failure-from-direct-finiteness-failure
kind: route
title: A scalar witness is a matrix witness at n equal to one
target: leavitt-group-algebra-not-stably-finite
requires: [leavitt-unit-group-algebra-not-directly-finite]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

Immediate: `M_1(F_2[G]) = F_2[G]`, so the pair `alpha, beta` demanded by the
prerequisite is a pair of `1x1` matrices with `beta alpha = I_1` and
`alpha beta != I_1` after renaming.

## Why it is recorded rather than folded away

This route is a trivial weakening, and it is the **only** link between the two
statements — nothing here reduces the matrix problem to the scalar one, so the
target does not collapse onto the prerequisite.  Recording it keeps the two
lanes correctly ordered: every route into the Kaplansky claim
(the corner lifting problems, the radical hypothesis, the whole-algebra lift
and the module splitting) reaches the surjunctivity lane through this step,
while a hypothetical witness at `n >= 2` would reach the target without
passing through the prerequisite at all.

It is the one place in this neighbourhood where a single-prerequisite route is
intended: the prerequisite is strictly stronger than the target, and the
statement it proves is one line, not a rename of the target.
