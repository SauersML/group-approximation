---
rg: 2
id: leavitt-direct-finiteness-failure-from-matrix-failure
kind: route
title: Compress a matrix witness of any size back to a scalar one
target: leavitt-unit-group-algebra-not-directly-finite
requires: [leavitt-group-algebra-not-stably-finite, leavitt-stable-finiteness-equals-direct-finiteness]
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

## Why sufficient

Immediate from the second prerequisite, which is established: stable
finiteness and direct finiteness coincide for `S = F_2[L_(F_2)(1,2)^x]`, so a
failure of the first is a failure of the second.

## Why the route is worth drawing

It is the **converse** of `stably-finite-failure-from-direct-finiteness-failure`,
which is the trivial `n = 1` direction, and drawing it makes the two claims
interderivable in the graph — which is the correct picture, and is the whole
content of the second prerequisite.

The value is negative and it is real: it removes matrix size as an independent
place to look.  Before this, `leavitt-group-algebra-not-stably-finite` was a
strictly weaker-looking target than the Kaplansky claim, and a witness at
`n >= 2` would have refuted Gottschalk's conjecture for `R^x` without
deciding Kaplansky's.  That option is gone.  Anyone tempted to search at
`n = 2` for room that `n = 1` does not have should read the second
prerequisite first: there is none.

## The cycle warning this route creates is intended — do not delete the route

`cairn check` now reports

    dependency cycle through claims: leavitt-group-algebra-not-stably-finite
      -> leavitt-unit-group-algebra-not-directly-finite
      -> leavitt-group-algebra-not-stably-finite

and that is exactly what an equivalence looks like in a kernel whose only
relation is `AND(requires) => target`.  Two claims that imply each other are
two routes forming a loop.  The fixpoint handles it correctly — neither claim
is established through the other, because a least fixpoint never fires a cycle
— so the warning is hygiene, not a defect, and silencing it by removing either
route would delete a true implication.  The companion route is
`stably-finite-failure-from-direct-finiteness-failure`.

## What it is not

It is not a reduction of anything to anything easier, and it should not be
read as progress toward either target.  Both prerequisites' claims are the
same problem wearing two shapes; the route says so explicitly rather than
leaving the graph to suggest that the matrix lane is a separate attack.  No
work is transferred and no hole is closed.
