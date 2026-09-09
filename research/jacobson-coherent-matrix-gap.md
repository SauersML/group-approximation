---
rg: 2
id: jacobson-coherent-matrix-gap
kind: claim
title: The coherent Jacobson quotient has a positive matrix gap in every dimension
distinct_from:
  jacobson-shift-mixed-gap: that asks for positivity of the original three-error problem; this imposes the additional nontrivial coherence word and studies a proper quotient with the head retained.
artifacts:
  - research/artifacts/jacobson-coherent-quotient-and-four-word-matrix-gap-2026-09-08.md
---

Prove `gamma_triangle>0` in the exact variational problem of
`jacobson-coherent-quotient-has-four-word-gap-criterion`.

The lower bound must hold for every matrix dimension and every complex
representation type of the prescribed finite groups, with the mark
retained. Neither a bounded-dimension calculation nor a correction
that loses operator-norm control supplies this assertion.

The completed third finite packet gives additional relations unavailable
in the old presentation. Its separate correction does not automatically
align its two rank-one restrictions with both old packets. The example in
`jacobson-third-packet-correction-must-move-an-edge` disproves a proposed
correction that freezes both restrictions, even in dimension eight.
That example kills the head and does not refute this gap.

The literal-group identification in
`jacobson-coherent-quotient-is-faithful-and-has-mf-dichotomy` makes this
the MF decision for one explicitly represented group. It does not decide
the sign of the infimum. No proof using property T or an infinite-group
almost-invariant-vector transport estimate qualifies for this route.
