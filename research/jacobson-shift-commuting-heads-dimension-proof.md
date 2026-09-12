---
rg: 2
id: jacobson-shift-commuting-heads-dimension-proof
kind: route
title: Centralize the shifted generators and count nontrivial factors in finite tensor summands
target: jacobson-shift-exact-representations-kill-head
requires:
  - jacobson-stable-letter-closes-boundary-recursion
artifacts:
  - research/artifacts/jacobson-shift-exact-collapse-and-monomial-gap-2026-09-08.md
---

The exact packet `B` makes the head commute with `tau(G)` and
`delta(G)`. The exact packet `C=C_0 x C_far` makes it commute
with `h_1`. These are the shifted generators, so the head centralizes
`alpha(H)`. Since the shifted generators are all old words,
`alpha(H)<=H`, and iteration gives pairwise commuting conjugate heads.

Decompose a representation of `G^n` into tensor products of irreducibles.
A summand supported on `s` nontrivial factors has dimension at least
`2^s>=2s`; perfectness excludes nontrivial one-dimensional factors.
If every factor acts nontrivially, summing over the summands gives
`d>=2n`. This contradicts the infinitely many conjugate heads in
any fixed dimension. Sections 1--3 of the artifact contain the proof.
