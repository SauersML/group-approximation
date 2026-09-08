---
rg: 2
id: nonhyperlinear-from-leavitt-24k-gap
kind: route
title: A dimension-uniform gap in the 24k problem produces a nonhyperlinear group
target: non-hyperlinear-group
requires:
  - leavitt-24k-feasibility-has-a-uniform-gap
  - binary-leavitt-hyperlinear-iff-24k-feasible
artifacts:
  - research/artifacts/leavitt-24k-relative-unitary-reduction-2026-09-08.md
---

By the second prerequisite, a dimension-uniform positive lower bound for one
relation set `T_m` is equivalent to failure of hyperlinearity for
`H = L_(F_2)(1,2)^x`.  That group exists and is nontrivial, so the target
follows immediately.

The reduction is stated in the direction that matters: the criterion's
right-to-left implication is proved with the separation constant recovered,
so a gap cannot be an artifact of a weakened separation requirement.  What the
route does not do is produce the gap; see the first prerequisite for what is
excluded so far, in particular that the first relation admits an exact finite
model and that the operator-norm gap already available does not transfer.
