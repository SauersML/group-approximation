---
rg: 2
id: thompson-f-no-two-transitive-via-disagreement-set-type
kind: route
title: No 2-transitive action of F, because its disagreement set would have to be neither a Cantor set nor a set with interior
target: thompson-f-has-no-faithful-2-transitive-action
requires:
  - thompson-f-two-transitive-disagreement-sets-are-self-similar
  - thompson-f-two-transitive-disagreement-sets-are-not-cantor
  - thompson-f-two-transitive-disagreement-sets-have-no-interior
---

Suppose `F` acts 2-transitively on `Ω` with `|Ω| ≥ 3`. Pick `ω ≠ ω'` and put
`D_0 = D(ω,ω')`.

1. By `thompson-f-two-transitive-disagreement-sets-have-no-interior`, `D_0` has
   empty interior.
2. By `thompson-f-two-transitive-disagreement-sets-are-not-cantor`, `D_0` has
   nonempty interior.

These contradict each other, so no 2-transitive action on at least 3 points
exists, faithful or not. That is the target.

The first prerequisite, `thompson-f-two-transitive-disagreement-sets-are-self-similar`,
is not used in the two lines above. It is listed because it explains why these
two cases are the only ones left: it already excludes disagreement sets with
finitely many components, including single intervals, finite sets and finite
unions of intervals. So each of the two OPEN halves can be attacked knowing that
`D_0` is perfect, has infinitely many components, and is an `F`-translate of
each of its nonempty clopen pieces.
